{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes, ExistentialQuantification #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
module Expr where
import Control.Arrow ((&&&))
import Data.List (intercalate)
import Data.Bits (xor)
import Control.Monad.Except
import Data.Proxy
import Data.Typeable
import qualified Data.Map as M

type Error = String
data Expr x = Val x | Var Name | Expr (Op x) [Parseable] deriving (Eq)
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

data Op y = Op { name :: Name, signature :: [ParseableType], fun :: [Parseable] -> y, fixity :: Fixity }
instance Show (Op y) where show op = name op
instance Eq (Op y) where a == b = name a == name b -- forall x y. name should be unique
appOp :: MonadError Error me => Op y -> [Parseable] -> me y
appOp op@(Op name signature fun _) ps
  | length ps /= opArity op = throwError $ show (length ps) ++ " args, but expected " ++ show (opArity op)
  | or $ zipWith (/=) signature (map parseableType ps) = throwError $ "Actual signature " ++ show (map parseableType ps) ++ " while expected " ++ show signature
  | otherwise = return $ fun ps

opArity :: Op y -> Arity
opArity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k -- k <- [1..]
opPrecedence :: Op y -> Precedence
opPrecedence op = case fixity op of
  Infix n -> n -- n <- [2..9]
  Prefix _ -> 10

-- TODO: TH for it
listify1 ab [a] = ab a
listify2 abc [a,b] = abc a b
listify3 abcd [a,b,c] = abcd a b c
-- short aliases for common ops
funop name signature original = Op name signature (listify1 original) (Prefix 1)
bifunop name signature original = Op name signature (listify2 original) (Prefix 2)
binop name signature original precedence = Op name signature (listify2 original) (InfixL precedence)
binopL = binop
binopR name signature original precedence = Op name signature (listify2 original) (InfixR precedence)

type Scope t = M.Map Name t

evalScope :: MonadError Error me => Scope x -> Expr x -> me x
evalScope _ (Val x)  = return x
evalScope m (Var var) = case M.lookup var m of
  Nothing -> throwError $ "variable " ++ var ++ " out of scope"
  Just x -> return x
evalScope m (Expr op xs) = fun op <$> traverse (evalScope m) xs

data ParseableType = forall x. Parse x => ParseableType (Proxy x)
instance Show ParseableType where show (ParseableType p) = show $ typeRep p
instance Eq ParseableType where a == b = show a == show b
data Parseable = forall x. Parse x => Parseable x
instance Show Parseable where show (Parseable p) = show p
instance Eq Parseable where -- TODO
parseableType :: Parseable -> ParseableType
parseableType (Parseable p) = ParseableType $ proxyOf p where
  proxyOf :: a -> Proxy a
  proxyOf _ = Proxy

class (Typeable x, Eq x, Read x, Show x) => Parse x where
  ops :: M.Map Name (Op x)
  defaultScope :: Scope x
  defaultScope = mempty
  eval :: Expr x -> Either Error x
  eval = evalScope defaultScope

double1 = [Proxy @Double]
double2 = [Proxy @Double, Proxy @Double]
double3 = [Proxy @Double, Proxy @Double, Proxy @Double]
binopD = flip binop double2
funopD = flip funop double1
instance Parse Double where
  ops = M.fromList $ map (name &&& id) $ [
    binopD "+" (+) 6,
    binopD "-" (-) 6,
    binopD "*" (*) 7,
    binopD "/" (/) 7,
    binopR "^" double2 (**) 8,
    funopD "sqrt" sqrt,
    funopD "~" negate,
    funopD "sin" sin,
    funopD "sinh" sinh,
    funopD "cos" cos,
    funopD "cosh" cosh,
    funopD "exp" exp,
    funopD "ln" log,
    bifunop "log" double3 logBase
    ]
  defaultScope = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]

bool1 = [Proxy @Bool]
bool2 = [Proxy @Bool, Proxy @Bool]
funopB = flip funop bool1
binopB = flip binop bool2
instance Parse Bool where
  ops = M.fromList $ map (name &&& id) $ [
    binopB "and" (&&) 3,
    binopB "&&" (&&) 3,
    binopB "or" (||) 2,
    binopB "||" (||) 2,
    binopB "xor" xor 6,
    binopB "==" (==) 6,
    funopB "not" not,
    funopB "~" not
    ]
  defaultScope = M.fromList [
    ("true", True),
    ("false", False),
    ("1", True),
    ("0", False)
    ]
