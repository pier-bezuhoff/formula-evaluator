{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Parser where
import Text.Read (readMaybe)
import Data.Proxy (Proxy(..))
import Data.Maybe
import Data.List.NonEmpty hiding (map, reverse, splitAt, length)
import qualified Data.List.NonEmpty as NEL
import Control.Monad
import Control.Monad.Except
import qualified Data.Map as M
import Parseable

-- L -> Val with one of types, V -> Var, O -> one of ops with fixed name
data Token = L AParseable | V Name | O AnOp Precedence deriving Show
-- matchs L and V ([U]nary)
pattern U token <- ((\token -> case token of L _ -> Just token; V _ -> Just token; _ -> Nothing) -> Just token)

opParams :: Parseable y => Op y -> (Name, [APType], [AParseable] -> AParseable, Fixity)
opParams (Op s ts f fixity) = (s, ts, AParseable <$> f, fixity)

-- try different strategies of parsing
tokenize :: forall me. MonadError Error me => String -> [me [Token]]
tokenize = go 1 . split where
  split' [] w = if null w then [] else [w]
  split' (c:s) w
    | c == '(' || c == ')' = (if null w then id else (w:)) $ [c] : split' s ""
    | c == ' ' || c == ',' || c == ';' = if null w then split' s "" else w : split' s ""
    | otherwise = split' s (c : w)
  split s = map reverse $ split' s ""
  readMaybeAPT :: APType -> String -> Maybe AParseable
  readMaybeAPT (APType p) = readMaybeAs p where
    readMaybeAs :: forall x. Parseable x => Proxy x -> String -> Maybe AParseable
    readMaybeAs _ s = AParseable <$> readMaybe @x s
  guessType :: String -> Token
  guessType w = case foldMap (maybeToList . flip readMaybeAPT w) parseableTypes of
    [] -> V w
    a:_ -> L a
  go :: Precedence -> [String] -> [me [Token]]
  go 1 [] = return $ return []
  go _ [] = return $ throwError "brackets doesn't match"
  go n (w:ws)
    | w == "(" = go (10 * n) ws -- NOTE: skip "()", "(())", ...
    | w == ")" = if n `rem` 10 == 0 then go (n `quot` 10) ws else return $ throwError "brackets doesn't match"
    | otherwise = case withNameInScope w fullOpScope of
        [] -> (fmap (guessType w :)) <$> go n ws -- prepend inside outer [] and MonadError
        -- here all possible ops are parsed
        ops -> do
          op <- ops
          goVariant <- go n ws
          return $ (O op (precedence' op * n) :) <$> goVariant

toRPN :: forall me. MonadError Error me => [Token] -> me [Token]
toRPN = go mempty 0 where
  popMax :: Ord k => M.Map k [v] -> Maybe ((k, v), M.Map k [v])
  popMax m
    | M.null m = Nothing
    | (k, v:vs) <- M.findMax m
    = Just ((k, v), M.updateMax(const $ if null vs then Nothing else Just vs) m)
    | otherwise = Nothing
  insert :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  insert k v m = M.insertWith (++) k [v] m
  -- setMax v m: m may NOT be null
  setMax :: Ord k => v -> M.Map k [v] -> M.Map k [v]
  setMax v m
    | (_, _:vs) <- M.findMax m
    = M.updateMax (const $ Just $ v:vs) m

  go :: M.Map Precedence [(AnOp, Arity)] -> Arity -> [Token] -> me [Token]
  go m 0 []
    | Just ((precedence, (op, _)), m') <- popMax m
    = if M.null m' then return [O op precedence]
      else let
        Just ((_, (_, arity)), _) = popMax m'
        in (O op precedence :) <$> go m' arity []
  go m _ []
    | M.null m = return []
  go m arity (l@(U _) : ts)
    | not (M.null m) && arity == 0
    , Just ((maxN, (op, _)), m') <- popMax m
    = if M.null m'
      then (O op maxN :) . (l:) <$> go m' (-1) ts
      else let
        Just ((_, (_, k)), _) = popMax m'
        in (O op maxN :) . (l:) <$> go m' (pred k) ts
    | otherwise = (l:) <$> go m (pred arity) ts
  go m k (O op n : ts)
    | M.null m = go (M.singleton n [(op, error "no matter")]) (k + arity' op) ts
    | otherwise = let
      Just ((maxN, (maxOp, _)), m') = popMax m
      Just ((_, (maxOp', maxArity')), _) = popMax m'
      prependMax = (O maxOp maxN :)
      insertNew arity = insert n (op, arity)
      single = M.singleton n [(op, error "no matter")]
      in case maxN `compare` n of
        EQ -> case fixity' op of -- -
          -- IL{I}...
          InfixL _ -> prependMax <$> go (insertNew 1 m') 1 ts
          InfixR _ -> case fixity' maxOp of
            InfixL _ -> prependMax <$> go (insertNew 1 m') 1 ts
            -- InfixR: special case: now >= 2 values in list at maxN
            InfixR _ -> go (insertNew 1 $ setMax (maxOp, 0) m) 1 ts
            Prefix _ -> throwError "infix and prefix ops cannot have the same fixity"
          -- P...(PL...L)({P}...
          Prefix arity -> if M.null m'
            then throwError $ "not enough (< " ++ show arity ++ ") args for " ++ show op
            else prependMax <$> go (insertNew arity $ setMax (maxOp', pred maxArity') m') arity ts
        GT -> case fixity' op of -- \
          Infix _ -> prependMax <$> if M.null m'
            then go single 1 ts
            else go m' maxArity' (O op n : ts)
          Prefix arity -> if k == 0
            then prependMax <$> go m' (pred maxArity') (O op n : ts)
            else go (insertNew arity m) k ts -- maybe impossible
        LT -> case fixity' op of -- /
          Infix _ -> go (insertNew 1 $ setMax (maxOp, k) m) 1 ts
          Prefix arity -> go (insertNew arity $ setMax (maxOp, pred k) m) arity ts
  go _ _ _ = throwError "bad syntax"

fromRPN :: forall me. MonadError Error me => [Token] -> me (Either FreeVar ATypedExpr)
fromRPN = go [] where
  ap2ate :: AParseable -> ATypedExpr
  ap2ate (AParseable p) = p2ate p where
    p2ate :: forall x. Parseable x => x -> ATypedExpr
    p2ate p = ATE $ TypedExpr (Val p) $ pType @x
  go :: [Either FreeVar ATypedExpr] -> [Token] -> me (Either FreeVar ATypedExpr)
  go [e] [] = return e
  go _ [] = throwError "unexpected end of expression"
  go stack (t:ts) = case t of
    L p -> go (Right (ap2ate p) : stack) ts
    V name -> go (Left (FreeVar name) : stack) ts
    O op _ -> if arity' op > length stack
      then throwError $ "not enough (< " ++ show (arity' op) ++ ") args for " ++ show op
      else let (start, rest) = splitAt (arity' op) stack
        in do
          e <- safeExpr @me op (reverse start)
          go (Right e : rest) ts

fromS :: forall me. MonadError Error me => [Token] -> me (Either FreeVar ATypedExpr)
fromS = undefined

parse :: MonadError Error me => String -> [me (Either FreeVar ATypedExpr)]
parse s = do
  tsVariant <- tokenize s
  return $ fromRPN =<< toRPN =<< tsVariant
