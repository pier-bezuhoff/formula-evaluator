{-# LANGUAGE LambdaCase, TypeApplications, ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns, PatternGuards #-}
module Parser where

import Data.Char
import Data.List (intercalate)
import Data.Bits (xor)
import Data.Maybe
import Control.Applicative
import Control.Arrow ((&&&))
import Control.Monad
import Text.Read (readMaybe)
import qualified Data.Map as M

data Expr x = Val x | Var Name | Expr (ExprOp x) [Expr x] deriving (Eq)
instance Show x => Show (Expr x) where
  show = \case
    Val x -> show x
    Var name -> name
    Expr op exprs -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ")"
eval :: Expr x -> M.Map Name x -> Maybe x
eval (Val x) _  = Just x
eval (Var x) m = M.lookup x m
eval (Expr op xs) m = fun op <$> traverse (`eval` m) xs
eval_ = (`eval` mempty)
eval' :: WithDefaults x => Expr x -> Maybe x
eval' = (`eval` defaults)
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

-- TODO: associativity!
type Precedence = Int -- [2..9]
data Fixity = Infix Precedence | Prefix Arity deriving (Show, Eq, Ord) -- Infix -> arity == 2
type Arity = Int -- [1..]
type Name = String

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
binop name original precedence = Op name (listify2 original) (Infix precedence)

data Token x = L Name | O (ExprOp x) Precedence deriving Show

class Ops x where ops :: M.Map Name (ExprOp x)
type Parse x = (Read x, Ops x)
instance Ops Double where
  ops = M.fromList $ map (name &&& id) $ [
    binop "+" (+) 6,
    binop "-" (-) 6,
    binop "*" (*) 7,
    binop "/" (/) 7,
    binop "^" (**) 8,
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
  go :: Parse x => M.Map Precedence (ExprOp x, Arity) -> Arity -> [Token x] -> Maybe [Token x]
  go m 0 []
    | not $ M.null m
    , ((n, (op, _)), m') <- M.deleteFindMax m
    = if M.null m'
      then Just [O op n]
      else let
        (_, (_, k)) = M.findMax m'
        in (O op n :) <$> go m' k []
  go m _ []
    | M.null m = Just []
  go m arity (l@(L _) : ts)
    | not (M.null m) && arity == 0
    , ((maxN, (op, _)), m') <- M.deleteFindMax m
    = if M.null m'
      then (O op maxN :) . (l:) <$> go m' (-1) ts
      else let
        (_, (_, k)) = M.findMax m'
        in (O op maxN :) . (l:) <$> go m' (pred k) ts
    | otherwise = (l:) <$> go m (pred arity) ts
  go m k (O op n : ts)
    | M.null m = go (M.singleton n (op, error "no matter")) (k + opArity op) ts
    | otherwise = let
    ((maxN, (maxOp, _)), m') = M.deleteFindMax m
    ((maxN', (maxOp', maxArity')), m'') = M.deleteFindMax m'
    prependMax = (O maxOp maxN :)
    insertNew arity m = M.insert n (op, arity) m
    single = M.singleton n (op, error "no matter")
    in case maxN `compare` n of
      EQ -> case fixity op of -- -
        -- IL{I}...
        Infix _ -> prependMax <$> go (insertNew 1 m') 1 ts
        -- P...(PL...L)({P}...
        Prefix arity -> let
          m'' = M.updateMax (const $ Just (maxOp', pred maxArity')) m'
          in if M.null m' then Nothing
          else prependMax <$> go (insertNew arity m'') arity ts
      GT -> case fixity op of -- \
        Infix _ -> prependMax <$> if M.null m'
          then go single 1 ts
          else go m' maxArity' (O op n : ts)
        Prefix arity -> if k == 0
          then prependMax <$> go m' (pred maxArity') (O op n : ts)
          else go (insertNew arity m) k ts -- maybe impossible
      LT -> case fixity op of -- /
        Infix _ -> go (insertNew 1 $ M.updateMax (const $ Just (maxOp, k)) m) 1 ts
        Prefix arity -> go (insertNew arity $ M.updateMax (const $ Just (maxOp, pred k)) m) arity ts
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

parseS :: Parse x => String -> Maybe (Expr x)
parseS = undefined

evalFile :: String -> IO ()
evalFile = undefined
{-
x = expr => add to vars map
expr => println
-}
