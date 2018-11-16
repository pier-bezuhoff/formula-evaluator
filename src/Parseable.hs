{-# LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
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
import Data.Typeable (cast, typeRep, Typeable, eqT)
import Data.Type.Equality ((:~:), gcastWith)
import qualified Data.Map as M

-- | Expr |
type Name = String
type Error = String
type Scope t = M.Map Name t

data Expr x = Val x APType | Var Name APType | Expr (Op x) [Expr AParseable] APType
instance Show x => Show (Expr x) where
  show = \case -- show as sexp
    Val x apt -> show x ++ " : " ++ show apt
    Var name apt -> name ++ " : " ++ show apt
    Expr op exprs apt -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ") : " ++ show apt

val :: forall x. Parseable x => x -> Expr x
val v = Val v $ pType @x

var :: forall x. Parseable x => Name -> Expr x
var s = Var s $ pType @x

expr :: forall x. Parseable x => Op x -> [Expr AParseable] -> Expr x
expr op exprs = Expr op exprs $ pType @x

-- NOTE: generalize :: Expr x -> Expr AParseable = fmap AParseable
-- NOTE: specialize :: Expr AParseable -> Maybe (Expr x) = gcast

evalScope' :: MonadError Error me => Scope AParseable -> Expr AParseable -> me AParseable
evalScope' m = \case
  Val x _ -> return x
  Var s apt -> case M.lookup s $ M.filter ((apt ==) . parseableType) m of
    Nothing -> throwError $ "variable " ++ s ++ " : " ++ show apt ++ " out of scope"
    Just x -> return x
  Expr op xs _ -> app op =<< traverse (evalScope' m) xs

-- QUESTION: maybe useless
evalScope :: forall x me. (Parseable x, MonadError Error me) => Scope AParseable -> Expr x -> me x
evalScope m = \case
  Val x _ -> return x
  Var var apt -> case M.lookup var (scopeOf @x m) of
    Nothing -> throwError $ "variable " ++ var ++ " : " ++ show apt ++ " out of scope"
    Just x -> return x
  Expr op xs _ -> app op =<< traverse (evalScope' m) xs

scopeOf :: forall x. Parseable x => Scope AParseable -> Scope x
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
data Op y = Op { name :: Name, signature :: [APType], fun :: [AParseable] -> y, fixity :: Fixity }

instance Show (Op y) where show op = name op
instance Eq (Op y) where a == b = name a == name b -- forall x y. name should be unique
instance Functor Op where fmap f op = op { fun = fmap f $ fun op }

app :: MonadError Error me => Op y -> [AParseable] -> me y
app op@(Op name pts fun _) ps
  | length ps /= arity op
  = throwError $ show (length ps) ++ " args, but expected " ++ show (arity op)
  | or $ zipWith (/=) pts (map parseableType ps)
  = throwError $ "Actual signature " ++ show (map parseableType ps) ++ ", while expected " ++ show pts
  | otherwise = return $ fun ps

arity :: Op y -> Arity
arity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k -- k <- [1..]
precedence :: Op y -> Precedence
precedence op = case fixity op of
  Infix n -> n -- n <- [2..9]
  Prefix _ -> 10
domain :: Op y -> APType
domain = head . signature
codomain :: forall y. Parseable y => Op y -> APType
codomain _ = APType (Proxy @y)

listify1 ab [a] = ab a
listify2 abc [a,b] = abc a b
listify3 abcd [a,b,c] = abcd a b c
-- short aliases for common ops
funop name pts f = Op name pts (listify1 f . fromJust . cast) (Prefix 1)
bifunop name pts f = Op name pts (listify2 $ cast2 f) (Prefix 2)
trifunop name pts f = Op name pts (listify3 $ cast3 f) (Prefix 2)
binop name pts f p = Op name pts (listify2 $ cast2 f) (InfixL p)
binopL name pts f = binop name pts f
binopR name pts f p = Op name pts (listify2 $ cast2 f) (InfixR p)
-- `fromJust` here are safe, because `app` check type matching
cast2 :: (Typeable a, Typeable b, Typeable c, Typeable d) => (c -> d -> e) -> a -> b -> e
cast2 f a b = fromJust (cast a) `f` fromJust (cast b)
cast3 :: (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable f) => (d -> e -> f -> x) -> a -> b -> c -> x
cast3 f a b c = f (fromJust $ cast a) (fromJust $ cast b) (fromJust $ cast b)


-- | AParseable |
data APType = forall x. Parseable x => APType (Proxy x)
instance Show APType where show (APType p) = show $ typeRep p
instance Eq APType where a == b = show a == show b

data AParseable = forall x. Parseable x => AParseable x
instance Show AParseable where show (AParseable p) = show p
instance Eq AParseable where
  AParseable a == AParseable b = let
    in case eq a b of
      Nothing -> False
      Just refl -> gcastWith refl $ a == b
pType :: forall x. Parseable x => APType
pType = APType $ Proxy @x
eq :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
eq _ _ = eqT
parseableType :: AParseable -> APType
parseableType (AParseable p) = APType $ pure p
getType :: Parseable x => proxy x -> APType
getType p = APType $ (const Proxy :: proxy x -> Proxy x) p

class (Typeable x, Eq x, Read x, Show x) => Parseable x where
  defaultScope :: Scope x
  defaultScope = mempty
  eval :: MonadError Error me => Expr x -> me x
  eval = evalScope $ fmap AParseable (defaultScope @x)

instance Parseable Double where
  defaultScope = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]

instance Parseable Bool where
  defaultScope = M.fromList [
    ("true", True),
    ("false", False)
    ]

r = APType $ Proxy @Double
b = APType $ Proxy @Bool
-- maybe use TH
parseableTypes :: [APType]
parseableTypes = [r, b]

funopD :: Name -> (Double -> Double) -> Op Double
funopD = flip funop [r]
binopD :: Name -> (Double -> Double -> Double) -> Precedence -> Op Double
binopD = flip binop [r, r]

funopB :: Name -> (Bool -> Bool) -> Op Bool
funopB = flip funop [b]
binopB :: Name -> (Bool -> Bool -> Bool) -> Precedence -> Op Bool
binopB = flip binop [b, b]

-- TODO: allow general (==), etc.
ops :: Scope (Op AParseable)
ops = M.fromList $ map (name &&& id) $ map generalize [
  -- first list :: [Op Double]
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
  bifunop "log" [r, r, r] logBase,
  trifunop "ifThenElse" [b, r, r] (\a b c -> if a then b else c)
  ] ++ map generalize [
  -- second list :: [Op Bool]
  binop "==" [r, r] ((==) :: Double -> Double -> Bool) 6,
  binop "!=" [r, r] ((/=) :: Double -> Double -> Bool) 6,

  binopB "and" (&&) 3,
  binopB "&&" (&&) 3,
  binopB "or" (||) 2,
  binopB "||" (||) 2,
  binopB "xor" xor 6,
  binopB "==" (==) 6,
  binopB "!=" (/=) 6,
  funopB "not" not,
  funopB "!" not,
  funopB "~" not,
  trifunop "ifThenElse" [b, b, b] (\a b c -> if a then b else c) :: Op Bool
  ] where
  generalize :: Parseable x => Op x -> Op AParseable
  generalize = fmap AParseable

opsFrom :: APType -> Scope (Op AParseable)
opsFrom pt = M.filter sameFrom ops where
  sameFrom op = pt == domain op
