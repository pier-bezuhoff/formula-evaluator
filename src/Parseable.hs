{-# LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
module Parseable where
import Control.Arrow ((&&&))
import Data.List (intercalate)
import Data.Bits (xor)
import Control.Monad.Except (MonadError, throwError)
import Data.Maybe (fromJust)
import Data.Proxy (Proxy(..))
import Data.Typeable (cast, typeRep, Typeable, eqT)
import Data.Type.Equality ((:~:), gcastWith)
import qualified Data.Map as M

-- | Expr |
type Name = String
type Error = String
type Scope t = M.Map Name t

data Expr x = Val x | Var Name  | Expr (Op x) [ATypedExpr]
instance Show x => Show (Expr x) where
  show = \case -- show as sexp
    Val x -> show x
    Var name -> name
    Expr op exprs -> "(" ++ show op ++ " " ++ intercalate " " (map show exprs) ++ ")"
instance Functor Expr where
  fmap f = \case
    Val x -> Val $ f x
    Var name -> Var name
    Expr op exprs -> Expr (fmap f op) exprs

data TypedExpr x = Parseable x => TypedExpr { te :: Expr x, apt :: APType }
instance Show x => Show (TypedExpr x) where
  show (TypedExpr e apt) = "(" ++ show e ++ " : " ++ show apt ++ show ")"

inferType :: forall x. Parseable x => Expr x -> TypedExpr x
inferType e = TypedExpr e $ pType @x

data ATypedExpr = forall x. Parseable x => ATE (TypedExpr x)
instance Show ATypedExpr where
  show (ATE te) = show te

evalScope' :: MonadError Error me => Scope AParseable -> ATypedExpr -> me AParseable
evalScope' m (ATE (TypedExpr te apt)) = case te of
  Val x -> return $ AParseable x
  Var s -> case M.lookup s $ M.filter ((apt ==) . parseableType) m of
    Nothing -> throwError $ "variable " ++ s ++ " : " ++ show apt ++ " out of scope"
    Just x -> return x
  Expr op xs -> fmap AParseable $ app op =<< traverse (evalScope' m) xs

evalScope :: (Parseable x, MonadError Error me) => Scope AParseable -> TypedExpr x -> me x
evalScope m (TypedExpr e apt) = fromJust . reifyAP <$> evalScope' m (ATE $ TypedExpr e apt)


-- | Op |
type Precedence = Int -- [2..9]
type Arity = Int -- [1..], number of args
-- Infix => arity == 2
data Fixity = InfixL Precedence | InfixR Precedence | Prefix Arity deriving (Show, Eq, Ord)
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

-- short aliases for common ops, arity and signatures should be checked in `app`
-- maybe use TH
op1 :: Parseable a => Name -> APType -> (a -> y) -> Op y
op1 name apt f = Op name [apt] f' (Prefix 1) where
  f' [AParseable a] = f $ fromJust $ maybeCast a
op2 :: (Parseable a, Parseable b) => Name -> APType -> APType -> (a -> b -> y) -> Fixity -> Op y
op2 name apt1 apt2 f fixity = Op name [apt1,apt2] f' fixity where
  f' [AParseable a, AParseable b] = fromJust (maybeCast a) `f` fromJust (maybeCast b)
op3 :: (Parseable a, Parseable b, Parseable c) => Name -> APType -> APType -> APType -> (a -> b -> c -> y) -> Op y
op3 name apt1 apt2 apt3 f = Op name [apt1,apt2,apt3] f' (Prefix 3) where
  f' [AParseable a, AParseable b, AParseable c] = f (fromJust $ maybeCast a) (fromJust $ maybeCast b) (fromJust $ maybeCast c)


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
reifyAP :: Parseable x => AParseable -> Maybe x
reifyAP (AParseable p) = maybeCast p

class (Typeable x, Eq x, Read x, Show x) => Parseable x where
  maybeCast :: Parseable y => x -> Maybe y
  maybeCast x = cast x
  defaultScope :: Scope x
  defaultScope = mempty
  eval :: MonadError Error me => TypedExpr x -> me x
  eval = evalScope $ AParseable <$> defaultScope @x

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


r = pType @Double
b = pType @Bool
-- maybe use TH
parseables :: [AParseable]
parseables = [AParseable (undefined :: Double), AParseable (undefined :: Bool)]
parseableTypes :: [APType]
parseableTypes = map parseableType parseables

funopD :: Name -> (Double -> Double) -> Op Double
funopD name = op1 name r
binopD :: Name -> (Double -> Double -> Double) -> Precedence -> Op Double
binopD name rrr p = op2 name r r rrr (InfixL p)

funopB :: Name -> (Bool -> Bool) -> Op Bool
funopB name = op1 name b
binopB :: Name -> (Bool -> Bool -> Bool) -> Precedence -> Op Bool
binopB name bbb p = op2 name b b bbb (InfixL p)

-- TODO: allow general (==), etc.
ops :: Scope (Op AParseable)
ops = M.fromList $ map (name &&& id) $ map generalize [
  -- first list :: [Op Double]
  binopD "+" (+) 6,
  binopD "-" (-) 6,
  binopD "*" (*) 7,
  binopD "/" (/) 7,
  op2 "^" r r (**) (InfixR 8),
  funopD "sqrt" sqrt,
  funopD "~" negate,
  funopD "sin" sin,
  funopD "sinh" sinh,
  funopD "cos" cos,
  funopD "cosh" cosh,
  funopD "exp" exp,
  funopD "ln" log,
  op2 "log" r r logBase (Prefix 2),
  op3 "ifThenElse" b r r (\a b c -> if a then b else c)
  ] ++ map generalize [
  -- second list :: [Op Bool]
  op2 "==" r r ((==) :: Double -> Double -> Bool) (InfixL 6),
  op2 "!=" r r ((/=) :: Double -> Double -> Bool) (InfixL 6),

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
  op3 "ifThenElse" b b b (\a b c -> if a then b else c)
  ] where
  generalize :: Parseable x => Op x -> Op AParseable
  generalize = fmap AParseable

opsFrom :: APType -> Scope (Op AParseable)
opsFrom pt = M.filter sameFrom ops where
  sameFrom op = pt == domain op
