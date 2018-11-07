{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
module Expr where
import Control.Arrow ((&&&))
import Data.List (intercalate)
import Data.Bits (xor)
import qualified Data.Map as M

type Error = String
data Expr x = Val x | Var Name | Expr (ExprOp x) [Expr x] deriving (Eq)
instance Show x => Show (Expr x) where
  show = \case -- show as sexp
    Val x -> show x
    Var name -> name
    Expr op exprs -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ")"

type Precedence = Int -- [2..9]
type Arity = Int -- [1..]
type Name = String
-- Infix => arity == 2
data Fixity = InfixL Precedence | InfixR Precedence | Prefix Arity
  deriving (Show, Eq, Ord)
pattern Infix :: Precedence -> Fixity
pattern Infix precedence <- (let
  f = \case
    InfixL p -> Just p
    InfixR p -> Just p
    _ -> Nothing
  in f -> Just precedence)

data Op x y = Op { name :: Name, fun :: [x] -> y, fixity :: Fixity }
instance Show (Op x y) where show op = name op
instance Eq (Op x y) where a == b = name a == name b -- forall x y. name should be unique

type ExprOp x = Op x x -- endomorphism

opArity :: Op x y -> Arity
opArity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k -- k <- [1..]
opPrecedence :: Op x y -> Precedence
opPrecedence op = case fixity op of
  Infix n -> n -- n <- [2..9]
  Prefix _ -> 10

listify1 ab [a] = ab a
listify2 abc [a,b] = abc a b
listify3 abcd [a,b,c] = abcd a b c
-- short aliases for common ops
funop name original = Op name (listify1 original) (Prefix 1)
bifunop name original = Op name (listify2 original) (Prefix 2)
binop name original precedence = Op name (listify2 original) (InfixL precedence)
binopL = binop
binopR name original precedence = Op name (listify2 original) (InfixR precedence)

type Scope t = M.Map Name t

evalScope :: Scope x -> Expr x -> Either Error x
evalScope _ (Val x)  = Right x
evalScope m (Var var) = case M.lookup var m of
  Nothing -> Left $ "variable " ++ var ++ " out of scope"
  Just x -> Right x
evalScope m (Expr op xs) = fun op <$> traverse (evalScope m) xs

class (Read x, Show x) => Parse x where
  ops :: M.Map Name (ExprOp x)
  defaultScope :: Scope x
  defaultScope = mempty
  eval :: Expr x -> Either Error x
  eval = evalScope defaultScope

instance Parse Double where
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
  defaultScope = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]

instance Parse Bool where
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
  defaultScope = M.fromList [
    ("true", True),
    ("false", False),
    ("1", True),
    ("0", False)
    ]
