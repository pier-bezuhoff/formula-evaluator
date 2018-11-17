{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Parser where
import Text.Read (readMaybe)
import Data.Monoid (First(..))
import Data.Proxy
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M
import Parseable

-- TODO: Token: O -> O [(AnOp, Precedence)] : op should be chosen after type check
-- L -> Val, V -> Var
data Token = L AParseable APType | V Name | O AnOp Precedence deriving Show
-- matchs L and V ([U]nary)
pattern U token <- ((\token -> case token of L _ _ -> Just token; V _ -> Just token; _ -> Nothing) -> Just token)
pattern O' s ts f fixity <- ((\(AnOp op) -> opParams op) -> (s, ts, f, fixity))

opParams :: Parseable y => Op y -> (Name, [APType], [AParseable] -> AParseable, Fixity)
opParams (Op s ts f fixity) = (s, ts, AParseable <$> f, fixity)

tokenize :: MonadError Error me => String -> me [Token]
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
  guessType w = case foldMap (First . flip readMaybeAPT w) parseableTypes of
    First Nothing -> V w
    First (Just a) -> L a (parseableType a)
  go 1 [] = return []
  go _ [] = throwError "brackets doesn't match"
  go n (w:ws)
    | w == "(" = go (10 * n) ws -- NOTE: skip "()", "(())", ...
    | w == ")" = if n `rem` 10 == 0 then go (n `quot` 10) ws else throwError "brackets doesn't match"
    | otherwise = case M.lookup w ops of
        Just op -> (O op (precedence' op * n) :) <$> go n ws
        Nothing -> (guessType w :) <$> go n ws

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
  ap2ate :: APType -> AParseable -> ATypedExpr
  ap2ate apt (AParseable p) = p2ate p where
    p2ate :: Parseable x => x -> ATypedExpr
    p2ate p = ATE $ TypedExpr (Val p) apt
  go :: [Either FreeVar ATypedExpr] -> [Token] -> me (Either FreeVar ATypedExpr)
  go [e] [] = return e
  go _ [] = throwError "unexpected end of expression"
  go stack (t:ts) = case t of
    L p apt -> go (Right (ap2ate apt p) : stack) ts
    V name -> go (Left (FreeVar name) : stack) ts
    O op _ -> if arity' op > length stack
      then throwError $ "not enough (< " ++ show (arity' op) ++ ") args for " ++ show op
      else let (start, rest) = splitAt (arity' op) stack
        in do
          e <- safeExpr @me op (reverse start)
          go (Right e : rest) ts

fromS :: forall me. MonadError Error me => [Token] -> me (Either FreeVar ATypedExpr)
fromS = undefined

parse :: MonadError Error me => String -> me (Either FreeVar ATypedExpr)
parse = fromRPN <=< toRPN <=< tokenize

processLine :: Scope AParseable -> String -> StateT (Scope AParseable) IO ()
processLine scope line = go where
  ws = words line
  s = intercalate " " $ tail $ ws
  doCarefully s expr answer action
    | Left err <- expr = liftIO $ reportParseError s err
    | Right expr' <- expr
    , Left err <- answer = liftIO $ reportEvalError s expr' err
    | otherwise = action
  evalOrFree :: MonadError Error me => Scope AParseable -> Either FreeVar ATypedExpr -> me AParseable
  evalOrFree scope = \case
    Left (FreeVar name) -> case M.lookup name scope of
      Nothing -> throwError $ "unknown free var " ++ name
      Just ap -> return $ ap
    Right ate -> evalScope' scope ate
  go = case ws of
    ":tokenize" : _ -> liftIO $ print $ tokenize @(Either String) s
    ":toRPN" : _ -> liftIO $ print $ toRPN @(Either String) =<< tokenize s
    ":parse" : _ -> liftIO $ print $ parse @(Either String) s
    ":parseRPN" : _ -> liftIO $ print $ fromRPN @(Either String) =<< tokenize s
    ":evalRPN" : _ -> liftIO $ print $ evalOrFree @(Either String) scope =<< fromRPN =<< tokenize s
    ":parseS" : _ -> liftIO $ print $ fromS @(Either String) =<< tokenize s
    ":evalS" : _ -> liftIO $ print $ evalOrFree @(Either String) scope =<< fromS =<< tokenize s
    ":help" : _ -> liftIO $ putStrLn help
    ":?" : _ -> liftIO $ putStrLn help
    _ : "=" : _ -> let
      s = intercalate " " $ drop 2 $ ws
      expr = parse @(Either String) s
      answer = evalOrFree @(Either String) scope =<< expr
      Right result = answer
      in doCarefully s expr answer $ put $ M.insert (head ws) result scope
    _ ->  let
      expr = parse @(Either String) line
      answer = evalOrFree @(Either String) scope =<< expr
      Right result = answer
      in doCarefully line expr answer $ liftIO $ putStrLn $ line ++ " = " ++ show result

reportParseError :: [Char] -> [Char] -> IO ()
reportParseError s err = putStrLn $ "Error while parsing expression at \"" ++ s ++ "\"\n\t" ++ err
reportEvalError :: Show a => [Char] -> a -> [Char] -> IO ()
reportEvalError s expr err = putStrLn $ "Error while evaluating expression \"" ++ s ++ "\"\n(parsed as " ++ show expr ++ ")\n\t" ++ err
help :: [Char]
help = "Available commands:\n" ++ (intercalate "\n" $ map ('\t':) $ [
  "<expresion> -- evaluate expression",
  "<statement> -- assign expresion in statement to variable",
  ":tokenize <expression>",
  ":toRPN <expression> -- toRPN <=< tokenize",
  ":parse <expression>",
  ":parseRPN <expression>",
  ":evalRPN <expression> -- evalScope scope <=< parseRPN",
  ":help or :?"
  ]) ++ "\n"

repl :: IO ()
repl = void $ runStateT processRepl fullDefaultScope where
  processRepl :: StateT (Scope AParseable) IO ()
  processRepl = do
    line <- liftIO $ getLine
    unless (line `elem` ["", "quit", "exit", ":q", ":Q", ":quit", ":exit"] || all (== ' ') line) $ do
      scope <- get
      processLine scope line
      processRepl

evalFile :: FilePath -> IO ()
evalFile filename = void $ runStateT process fullDefaultScope where
  process :: StateT (Scope AParseable) IO ()
  process = do
    content <- liftIO $ readFile filename
    forM_ (lines content) $ \line -> do
      m <- get
      processLine m line
    m <- get
    liftIO $ forM_ (M.toList m) $ \(k, v) ->
      putStrLn $ k ++ " = " ++ show v
