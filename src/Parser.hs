{-# LANGUAGE LambdaCase, TypeApplications, ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns, PatternGuards #-}
module Parser where

import Data.List (intercalate)
import Data.Bits (xor)
import Text.Read (readMaybe)
import Control.Arrow ((&&&))
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.State
import qualified Data.Map as M

data Expr x = Val x | Var Name | Expr (ExprOp x) [Expr x] deriving (Eq)
instance Show x => Show (Expr x) where
  show = \case
    Val x -> show x
    Var name -> name
    Expr op exprs -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ")"
eval :: M.Map Name x -> Expr x -> Maybe x
eval _ (Val x)  = Just x
eval m (Var x) = M.lookup x m
eval m (Expr op xs) = fun op <$> traverse (eval m) xs
eval_ = eval mempty
eval' :: WithDefaults x => Expr x -> Maybe x
eval' = eval defaults
class Parse x => WithDefaults x where defaults :: M.Map Name x
instance WithDefaults Double where
  defaults = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]
instance WithDefaults Bool where
  defaults = M.fromList [
    ("true", True),
    ("false", False),
    ("1", True),
    ("0", False)
    ]

type Precedence = Int -- [2..9]
type Arity = Int -- [1..]
type Name = String
data Fixity = InfixL Precedence | InfixR Precedence | Prefix Arity deriving (Show, Eq, Ord) -- Infix -> arity == 2
pattern Infix precedence <- (let
  f = \case
    InfixL p -> Just p
    InfixR p -> Just p
    _ -> Nothing
  in f -> Just precedence)

data Op x y = Op { name :: Name, fun :: [x] -> y, fixity :: Fixity }
type ExprOp x = Op x x
instance Show (Op x y) where show op = name op
instance Eq (Op x y) where a == b = name a == name b
opArity :: Op x y -> Arity
opArity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k
opPrecedence :: Op x y -> Precedence
opPrecedence op = case fixity op of
  Infix n -> n
  Prefix _ -> 10

listify1 ab [a] = ab a
listify2 abc [a,b] = abc a b
listify3 abcd [a,b,c] = abcd a b c
funop name original = Op name (listify1 original) (Prefix 1)
bifunop name original = Op name (listify2 original) (Prefix 2)
binop name original precedence = Op name (listify2 original) (InfixL precedence)
binopL = binop
binopR name original precedence = Op name (listify2 original) (InfixR precedence)

data Token x = L Name | O (ExprOp x) Precedence deriving Show

class Ops x where ops :: M.Map Name (ExprOp x)
type Parse x = (Read x, Ops x)
instance Ops Double where
  ops = M.fromList $ map (name &&& id) $ [
    binop "+" (+) 6,
    binop "-" (-) 6,
    binop "*" (*) 7,
    binop "/" (/) 7,
    binopR "^" (**) 8,
    funop "sqrt" sqrt,
    funop "~" negate,
    funop "sin" sin,
    funop "sinh" sinh,
    funop "cos" cos,
    funop "cosh" cosh,
    funop "exp" exp,
    funop "ln" log,
    bifunop "log" logBase
    ]
instance Ops Bool where
  ops = M.fromList $ map (name &&& id) $ [
    binop "and" (&&) 3,
    binop "&&" (&&) 3,
    binop "or" (||) 2,
    binop "||" (||) 2,
    binop "xor" xor 6,
    binop "==" (==) 6,
    funop "not" not,
    funop "~" not
    ]

tokenize :: Parse x => String -> Maybe [Token x]
tokenize = go 1 . split where
  split' [] w = if null w then [] else [w]
  split' (c:s) w
    | c == '(' || c == ')' = (if null w then id else (w:)) $ [c] : split' s ""
    | c == ' ' || c == ',' || c == ';' = if null w then split' s "" else w : split' s ""
    | otherwise = split' s (c : w)
  split s = map reverse $ split' s ""
  go 1 [] = Just []
  go _ [] = Nothing -- brackets should match
  go n (w:ws)
    | w == "(" = go (10 * n) ws -- NOTE: skip "()", "(())", ...
    | w == ")" = if n `rem` 10 == 0 then go (n `quot` 10) ws else Nothing
    | otherwise = case M.lookup w ops of
        Just op -> (O op (opPrecedence op * n) :) <$> go n ws
        Nothing -> (L w :) <$> go n ws

toRPN :: Parse x => [Token x] -> Maybe [Token x]
toRPN = go mempty 0 where
  pop :: Ord k => k -> M.Map k [v] -> Maybe (v, M.Map k [v])
  pop k m
    | Just (v:vs) <- m M.!? k
    = Just (v, M.update (const $ if null vs then Nothing else Just vs) k m)
    | otherwise = Nothing
  popMax :: Ord k => M.Map k [v] -> Maybe ((k, v), M.Map k [v])
  popMax m
    | M.null m = Nothing
    | (k, v:vs) <- M.findMax m
    = Just ((k, v), M.updateMax(const $ if null vs then Nothing else Just vs) m)
  insert :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
  insert k v m = M.insertWith (++) k [v] m
  -- setMax v m: m may NOT be null
  setMax :: Ord k => v -> M.Map k [v] -> M.Map k [v]
  setMax v m
    | (_, _:vs) <- M.findMax m
    = M.updateMax (const $ Just $ v:vs) m

  go :: Parse x => M.Map Precedence [(ExprOp x, Arity)] -> Arity -> [Token x] -> Maybe [Token x]
  go m 0 []
    | Just ((precedence, (op, _)), m') <- popMax m
    = if M.null m' then Just [O op precedence]
      else let
        Just ((_, (_, arity)), _) = popMax m'
        in (O op precedence :) <$> go m' arity []
  go m _ []
    | M.null m = Just []
  go m arity (l@(L _) : ts)
    | not (M.null m) && arity == 0
    , Just ((maxN, (op, _)), m') <- popMax m
    = if M.null m'
      then (O op maxN :) . (l:) <$> go m' (-1) ts
      else let
        Just ((_, (_, k)), _) = popMax m'
        in (O op maxN :) . (l:) <$> go m' (pred k) ts
    | otherwise = (l:) <$> go m (pred arity) ts
  go m k (O op n : ts)
    | M.null m = go (M.singleton n [(op, error "no matter")]) (k + opArity op) ts
    | otherwise = let
      Just ((maxN, (maxOp, _)), m') = popMax m
      Just ((maxN', (maxOp', maxArity')), m'') = popMax m'
      prependMax = (O maxOp maxN :)
      insertNew arity m = insert n (op, arity) m
      single = M.singleton n [(op, error "no matter")]
      in case maxN `compare` n of
        EQ -> case fixity op of -- -
          -- IL{I}...
          InfixL _ -> prependMax <$> go (insertNew 1 m') 1 ts
          InfixR _ -> case fixity maxOp of
            InfixL _ -> prependMax <$> go (insertNew 1 m') 1 ts
            -- InfixR: special case: now >= 2 values in list at maxN
            InfixR _ -> go (insertNew 1 $ setMax (maxOp, 0) m) 1 ts
          -- P...(PL...L)({P}...
          Prefix arity -> if M.null m'
            then Nothing
            else prependMax <$> go (insertNew arity $ setMax (maxOp', pred maxArity') m') arity ts
        GT -> case fixity op of -- \
          Infix _ -> prependMax <$> if M.null m'
            then go single 1 ts
            else go m' maxArity' (O op n : ts)
          Prefix arity -> if k == 0
            then prependMax <$> go m' (pred maxArity') (O op n : ts)
            else go (insertNew arity m) k ts -- maybe impossible
        LT -> case fixity op of -- /
          Infix _ -> go (insertNew 1 $ setMax (maxOp, k) m) 1 ts
          Prefix arity -> go (insertNew arity $ setMax (maxOp, pred k) m) arity ts
  go _ _ _ = Nothing

fromRPN :: Parse x => [Token x] -> Maybe (Expr x)
fromRPN = go [] where
  fromL l = fromMaybe (Var l) $ Val <$> readMaybe l
  grab op stack
    | opArity op > length stack = const Nothing -- not enough args to op
    | otherwise = case opArity op of
      1 -> let (a:rest) = stack in go (Expr op [a] : rest)
      2 -> let (b:a:rest) = stack in go (Expr op [a,b] : rest)
      3 -> let (c:b:a:rest) = stack in go (Expr op [a,b,c] : rest)
      _ -> const Nothing -- strange arity
  go :: Read x => [Expr x] -> [Token x] -> Maybe (Expr x)
  go [x] [] = Just x
  go _ [] = Nothing
  go stack (t:ts) = case t of
    L l -> go (fromL l : stack) ts
    O op _ -> grab op stack ts
    
parse :: Parse x => String -> Maybe (Expr x)
parse = fromRPN <=< toRPN <=< tokenize

parseRPN :: Parse x => String -> Maybe (Expr x)
parseRPN = go [] . words where
  go [x] [] = Just x
  go _ [] = Nothing
  go stack (s:rest) = let mv = readMaybe s in
    case mv of
      Just v -> go (Val v : stack) rest
      Nothing -> let mop = M.lookup s ops in
        case mop of
          Nothing -> go (Var s : stack) rest
          Just op ->
            case opArity op of
              1 -> let (a:xs) = stack in go (Expr op [a] : xs) rest
              2 -> let (b:a:xs) = stack in go (Expr op [a,b] : xs) rest
              3 -> let (c:b:a:xs) = stack in go (Expr op [a,b,c] : xs) rest
              arity -> error $ "unexpected arity: " ++ show arity

parseS :: Parse x => String -> Maybe (Expr x)
parseS = undefined

evalFile :: FilePath -> IO ()
evalFile filename = void $ runStateT (process @Double) defaults where
  reportParseError s = putStrLn $ "ERROR: Failed to parse expression:" ++ s
  reportEvalError s expr = putStrLn $ "ERROR: Failed to evaluate expression:" ++ s ++ "\n(parsed as " ++ show (fromJust expr) ++ ")"
  processStatement :: (Show t, WithDefaults t) => M.Map Name t -> String -> StateT (M.Map Name t) IO ()
  processStatement m statement = do
    let ws = words statement
    if length ws > 2 && ws !! 1 == "="
      then let
        s = drop (2 + fromJust (findIndex (== '=') statement)) statement
        expr = parse s
        answer = eval m =<< expr
        in if isNothing expr then liftIO $ reportParseError s
        else if isNothing answer then liftIO $ reportEvalError s expr
        else put $ M.insert (ws !! 0) (fromJust answer) m
    else let
      expr = parse statement
      answer = eval m =<< expr
      in if isNothing expr then liftIO $ reportParseError statement
      else if isNothing answer then liftIO $ reportEvalError statement expr
      else liftIO $ putStrLn $ statement ++ " = " ++ show (fromJust answer)
  process :: (Show t, WithDefaults t) => StateT (M.Map Name t) IO ()
  process = do
    content <- liftIO $ readFile filename
    forM_ (lines content) $ \line -> do
      m <- get
      processStatement m line
    m <- get
    liftIO $ forM_ (M.toList m) $ \(k, v) ->
      putStrLn $ k ++ " = " ++ show v
