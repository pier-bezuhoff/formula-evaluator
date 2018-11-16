{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
module Parseable where
import Control.Arrow ((&&&))
import Data.List (intercalate)
import Data.Bits (xor)
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (isJust, fromJust)
import Data.Proxy (Proxy(..))
import Data.Typeable (gcast, cast, typeRep, Typeable, eqT)
import Data.Type.Equality ((:~:), gcastWith)
import qualified Data.Map as M

-- | Expr |
type Name = String
type Error = String
type Scope t = M.Map Name t

data Expr x = Val x | Var Name | Expr (Op x) [Expr Parseable]
instance Show x => Show (Expr x) where
  show = \case -- show as sexp
    Val x -> show x
    Var name -> name
    Expr op exprs -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ")"
instance Functor Expr where
  fmap f (Val x) = Val $ f x
  fmap _ (Var s) = Var s
  fmap f (Expr op ps) = Expr (fmap f op) ps
-- NOTE: generalize :: Expr x -> Expr Parseable = fmap Parseable
-- NOTE: specialize :: Expr Parseable -> Maybe (Expr x) = gcast
-- NOTE: reify :: Expr Parseable -> (forall x. Parse x => Expr x) = fmap reifyP

evalScope' :: MonadError Error me => Scope Parseable -> Expr Parseable -> me Parseable
evalScope' m = \case
  Val x -> return x


evalScope :: forall x me. (Parse x, MonadError Error me) => Scope Parseable -> Expr x -> me x
evalScope _ (Val x)  = return x
evalScope m (Var var) = case M.lookup var (scopeOf @x m) of
  Nothing -> throwError $ "variable " ++ var ++ " out of scope"
  Just x -> return x
evalScope m (Expr op xs) = app op =<< traverse g xs where
  g = fmap Parseable . f . fmap reifyP
  f :: Parse x => Expr x -> me x
  f = evalScope m

scopeOf :: forall x. Parse x => Scope Parseable -> Scope x
scopeOf = mCatMaybes . fmap cast

mCatMaybes :: M.Map k (Maybe x) -> M.Map k x
mCatMaybes = fmap fromJust . M.filter (isJust)

-- | Op |
type Precedence = Int -- [2..9]
type Arity = Int -- [1..], number of args
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

-- signature should not be empty
data Op y = Op { name :: Name, signature :: [ParseableType], fun :: [Parseable] -> y, fixity :: Fixity }

instance Show (Op y) where show op = name op
instance Eq (Op y) where a == b = name a == name b -- forall x y. name should be unique
instance Functor Op where fmap f op = op { fun = fmap f $ fun op }

app :: MonadError Error me => Op y -> [Parseable] -> me y
app op@(Op name pts fun _) ps
  | length ps /= arity op
  = throwError $ show (length ps) ++ " args, but expected " ++ show (arity op)
  | or $ zipWith (/=) pts (map parseableType ps)
  = throwError $ "Actual pts " ++ show (map parseableType ps) ++ " while expected " ++ show pts
  | otherwise = return $ fun ps

arity :: Op y -> Arity
arity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k -- k <- [1..]
precedence :: Op y -> Precedence
precedence op = case fixity op of
  Infix n -> n -- n <- [2..9]
  Prefix _ -> 10
domain :: Op y -> ParseableType
domain = head . signature
codomain :: forall y. Parse y => Op y -> ParseableType
codomain _ = ParseableType (Proxy @y)

listify1 ab [a] = ab a
listify2 abc [a,b] = abc a b
listify3 abcd [a,b,c] = abcd a b c
-- short aliases for common ops
funop name pts f = Op name pts (listify1 f) (Prefix 1)
bifunop name pts f = Op name pts (listify2 f) (Prefix 2)
binop name pts f p = Op name pts (listify2 f) (InfixL p)
binopL = binop
binopR name pts f p = Op name pts (listify2 f) (InfixR p)


-- | Parseable |
data ParseableType = forall x. Parse x => ParseableType (Proxy x)
instance Show ParseableType where show (ParseableType p) = show $ typeRep p
instance Eq ParseableType where a == b = show a == show b

data Parseable = forall x. Parse x => Parseable x
instance Show Parseable where show (Parseable p) = show p
instance Eq Parseable where
  Parseable a == Parseable b = let
    in case eq a b of
      Nothing -> False
      Just refl -> gcastWith refl $ a == b

eq :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
eq _ _ = eqT
parseableType :: Parseable -> ParseableType
parseableType (Parseable p) = ParseableType $ pure p
getType :: Parse x => proxy x -> ParseableType
getType p = ParseableType $ (const Proxy :: proxy x -> Proxy x) p
innerType :: Functor proxy => proxy Parseable -> ParseableType
innerType = extract . fmap parseableType where
  extract :: Functor proxy => proxy ParseableType -> ParseableType
  extract p = ParseableType Proxy -- TODO: extract somehow

class (Typeable x, Eq x, Read x, Show x) => Parse x where
  defaultScope :: Scope x
  defaultScope = mempty
  eval :: MonadError Error me => Expr x -> me x
  eval = evalScope $ fmap Parseable (defaultScope @x)

instance Parse Double where
  defaultScope = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]

instance Parse Bool where
  defaultScope = M.fromList [
    ("true", True),
    ("false", False)
    ]

r = ParseableType $ Proxy @Double
b = ParseableType $ Proxy @Bool
-- maybe use TH
parseableTypes :: [ParseableType]
parseableTypes = [r, b]

funopD :: Name -> ([Parseable] -> Double) -> Op Double
funopD = flip funop [r]
binopD :: Name -> ([Parseable] -> Double) -> Fixity -> Op Double
binopD = flip binop [r, r]

funopB :: Name -> ([Parseable] -> Bool) -> Op Bool
funopB = flip funop [b]
binopB :: Name -> ([Parseable] -> Bool) -> Fixity -> Op Bool
binopB = flip binop [b, b]

-- TODO: allow general (==), etc.
ops :: Scope (Op Parseable)
ops = M.fromList $ map (name &&& generalize) $ [
  binopD "+" (+) 6,
  binopD "-" (-) 6,
  binopD "*" (*) 7,
  binopD "/" (/) 7,
  binopR "^" [r, r] (**) 8 :: Op Double,
  funopD "sqrt" sqrt,
  funopD "~" negate,
  funopD "sin" sin,
  funopD "sinh" sinh,
  funopD "cos" cos,
  funopD "cosh" cosh,
  funopD "exp" exp,
  funopD "ln" log,
  bifunop "log" [r, r, r] logBase :: Op Double,
  bifunop "ifThenElse" [b, r, r] (\a b c -> if a then b else c) :: Op Double,
  binop [r, r] (==) 6 :: Op Double,
  binop [r, r] (/=) 6 :: Op Double,

  binopB "and" (&&) 3,
  binopB "&&" (&&) 3,
  binopB "or" (||) 2,
  binopB "||" (||) 2,
  binopB "xor" xor 6,
  binopB "==" (==) 6,
  binopB "!=" (/=) 6,
  funopB "not" not,
  funopB "!" not,
  bifunop "ifThenElse" [b, b, b] (\a b c -> if a then b else c) :: Op Bool
  ] where
  generalize :: Parse x => Op x -> Op Parseable
  generalize = fmap Parseable

opsFrom :: ParseableType -> Scope (Op Parseable)
opsFrom pt = M.filter sameFrom ops where
  sameFrom op = pt == domain op

opsTo :: forall y proxy. Parse y => proxy y -> Scope (Op y)
opsTo _ = M.filter sameTo ops where
  sameTo op = ParseableType (Proxy @y) == codomain op
