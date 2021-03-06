{-# LANGUAGE FlexibleContexts, AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes, ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE TypeApplications, TypeOperators #-}
module Parseable where
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

data AnExpr = forall x. Parseable x => AnExpr (Expr x)
instance Show AnExpr where show (AnExpr e) = show e

data FreeVar = FreeVar Name deriving (Show, Eq)

captureFreeVar :: APType -> FreeVar -> ATypedExpr
captureFreeVar apt@(APType pt) (FreeVar name) = pt2ate pt where
  pt2ate :: forall x. Parseable x => Proxy x -> ATypedExpr
  pt2ate _ = ATE $ TypedExpr @x (Var name) apt

safeExpr :: MonadError Error me => AnOp -> [Either FreeVar ATypedExpr] -> me ATypedExpr
safeExpr (AnOp op) es
  | length es /= arity op
  = throwError $ show op ++ " arity is " ++ show (arity op) ++ ", while supplied " ++ show (length es) ++ " args"
  | not $ and $ zipWith cmpType es (signature op)
  = throwError $ show op ++ " signature is " ++ show (signature op) ++ ", but got " ++ show (map toMAPT es)
  | otherwise
  = return $ ATE $ flip TypedExpr (codomain op) $ Expr op $ zipWith toATE es $ signature op where
    cmpType (Left (FreeVar _)) _ = True
    cmpType (Right (ATE (TypedExpr _ t))) apt = t == apt
    toMAPT (Left _) = Wildcard
    toMAPT (Right (ATE (TypedExpr _ t))) = APT t
    toATE (Right ate) _ = ate
    toATE (Left (FreeVar name)) t = captureFreeVar t (FreeVar name)

data TypedExpr x = Parseable x => TypedExpr { te :: Expr x, apt :: APType }
instance Show x => Show (TypedExpr x) where
  show (TypedExpr e t) = "(" ++ show e ++ " : " ++ show t ++ ")"

inferType :: forall x. Parseable x => Expr x -> TypedExpr x
inferType e = TypedExpr e $ pType @x

data ATypedExpr = forall x. Parseable x => ATE (TypedExpr x)
instance Show ATypedExpr where
  show (ATE te) = show te

evalScope' :: MonadError Error me => Scope AParseable -> ATypedExpr -> me AParseable
evalScope' m (ATE (TypedExpr te t)) = case te of
  Val x -> return $ AParseable x
  Var s -> case M.lookup s $ M.filter ((t ==) . parseableType) m of
    Nothing -> throwError $ "variable " ++ s ++ " : " ++ show t ++ " out of scope"
    Just x -> return x
  Expr op xs -> fmap AParseable $ app op =<< traverse (evalScope' m) xs

evalScope :: (Parseable x, MonadError Error me) => Scope AParseable -> TypedExpr x -> me x
evalScope m (TypedExpr e t) = fromJust . reifyAP <$> evalScope' m (ATE $ TypedExpr e t)


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

prettyO :: forall y. Parseable y => Op y -> String
prettyO (Op name signature _ fixity) = name ++ " : " ++ show signature ++ " -> " ++ show (pType @y) ++ " {" ++ show fixity ++ "}"

data AnOp = forall y. Parseable y => AnOp (Op y)
instance Show AnOp where show (AnOp op) = show op
instance Eq AnOp where
  AnOp op == AnOp op' = let
    eq :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
    eq _ _ = eqT
    in case eq op op' of
      Nothing -> False
      Just refl -> gcastWith refl $ op == op'

prettyAO :: AnOp -> String
prettyAO (AnOp op) = prettyO op

anOp :: Parseable y => Op y -> AnOp
anOp = AnOp

app :: MonadError Error me => Op y -> [AParseable] -> me y
app op@(Op _ pts fun _) ps
  | length ps /= arity op
  = throwError $ show (length ps) ++ " args, but expected " ++ show (arity op)
  | or $ zipWith (/=) pts (map parseableType ps)
  = throwError $ "Actual signature " ++ show (map parseableType ps) ++ ", while expected " ++ show pts
  | otherwise = return $ fun ps

name' :: AnOp -> Name
name' (AnOp op) = name op
arity :: Op y -> Arity
arity op = case fixity op of
  Infix _ -> 2
  Prefix k -> k -- k <- [1..]
arity' :: AnOp -> Arity
arity' (AnOp op) = arity op
fixity' :: AnOp -> Fixity
fixity' (AnOp op) = fixity op
precedence :: Op y -> Precedence
precedence op = case fixity op of
  Infix n -> n -- n <- [2..9]
  Prefix _ -> 10
precedence' :: AnOp -> Precedence
precedence' (AnOp op) = precedence op
domain :: Op y -> APType
domain = head . signature
codomain :: forall y. Parseable y => Op y -> APType
codomain _ = APType (Proxy @y)
codomain' :: AnOp -> APType
codomain' (AnOp op) = codomain op

-- short aliases for common ops, arity and signatures should be checked in `app`
-- maybe use TH
op1 :: forall a y. Parseable a => Name -> (a -> y) -> Op y
op1 name f = Op name [pType @a] f' (Prefix 1) where
  f' [AParseable a] = f $ cast' a
op2 :: forall a b y. (Parseable a, Parseable b) => Name -> (a -> b -> y) -> Fixity -> Op y
op2 name f fixity = Op name [pType @a, pType @b] f' fixity where
  f' [AParseable a, AParseable b] = cast' a `f` cast' b
op3 :: forall a b c y. (Parseable a, Parseable b, Parseable c) => Name -> (a -> b -> c -> y) -> Op y
op3 name f = Op name [pType @a, pType @b, pType @c] f' (Prefix 3) where
  f' [AParseable a, AParseable b, AParseable c] = f (cast' a) (cast' b) (cast' c)


-- | Parseable |
-- a parseable type
data APType = forall x. Parseable x => APType (Proxy x)
instance Show APType where show (APType p) = show $ typeRep p
instance Eq APType where a == b = show a == show b
instance Ord APType where a `compare` b = show a `compare` show b

pType :: forall x. Parseable x => APType
pType = APType $ Proxy @x
getType :: Parseable x => proxy x -> APType
getType p = APType $ (const Proxy :: proxy x -> Proxy x) p
reifyAPT :: forall x. Parseable x => APType -> Maybe (Proxy x)
reifyAPT (APType p) = castable p where
  castable :: (Parseable a, Parseable b) => Proxy a -> Maybe (Proxy b)
  castable = cast

data MaybeAPT = APT APType | Wildcard deriving (Eq)
instance Show MaybeAPT where
  show Wildcard = "?"
  show (APT apt) = show apt

data AParseable = forall x. Parseable x => AParseable x
instance Show AParseable where show ap@(AParseable p) = show p ++ " : " ++ show (parseableType ap)
instance Eq AParseable where
  AParseable a == AParseable b = let
    eq :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
    eq _ _ = eqT
    in case eq a b of
      Nothing -> False
      Just refl -> gcastWith refl $ a == b

parseableType :: AParseable -> APType
parseableType (AParseable p) = APType $ pure p
apt2ap :: APType -> AParseable -- NOTE: hold undefined
apt2ap (APType p) = AParseable $ instantiate p where
  instantiate :: Proxy x -> x
  instantiate Proxy = undefined
reifyAP :: forall x. Parseable x => AParseable -> Maybe x
reifyAP (AParseable p) = cast p

-- use `fromJust`, types MUST be `cast`-able
cast' :: (Parseable x, Parseable y) => x -> y
cast' = fromJust . cast

eval :: forall x me. (Parseable x, MonadError Error me) => TypedExpr x -> me x
eval = evalScope $ AParseable <$> defaultScope @x

type TypedScope = M.Map (String, [APType])
-- parametrized by name, domain and codomain
typedAOScope :: [AnOp] -> TypedScope AnOp
typedAOScope = M.fromList . map (\(AnOp op) -> ((name op, getType op : signature op), AnOp op))

withNameInScope :: String -> TypedScope x -> [x]
withNameInScope key = M.elems . M.filterWithKey (\(name, _) _ -> name == key)

class (Typeable x, Eq x, Read x, Show x) => Parseable x where
  defaultScope :: Scope x
  defaultScope = mempty
  defaultOpScope :: proxy x -> TypedScope AnOp
  defaultOpScope _ = typedAOScope $ map anOp [
    op2 @x @x "==" (==) (InfixL 6),
    op2 @x @x "!=" (/=) (InfixL 6)
    ] ++ map anOp [
    op3 @Bool @x @x "ifThenElse" (\a b c -> if a then b else c)
    ]
  opScope :: proxy x -> TypedScope AnOp
  opScope _ = mempty

instance Parseable Double where
  defaultScope = M.fromList [
    ("e", exp 1),
    ("pi", pi)
    ]
  opScope _ = typedAOScope $ map (anOp :: Op Double -> AnOp) [
    op2 "+" (+) (InfixL 6),
    op2 "-" (-) (InfixL 6),
    op2 "*" (*) (InfixL 7),
    op2 "/" (/) (InfixL 7),
    op2 "^" (**) (InfixR 8),
    op1 "sqrt" sqrt,
    op1 "~" negate,
    op1 "sin" sin,
    op1 "sinh" sinh,
    op1 "cos" cos,
    op1 "cosh" cosh,
    op1 "exp" exp,
    op1 "ln" log,
    op2 "log" logBase (Prefix 2)
    ]

instance Parseable Bool where
  defaultScope = M.fromList [
    ("true", True),
    ("false", False)
    ]
  opScope _ = typedAOScope $ map (anOp :: Op Bool -> AnOp) [
    op2 "and" (&&) (InfixL 3),
    op2 "&&" (&&) (InfixL 3),
    op2 "or" (||) (InfixL 2),
    op2 "||" (||) (InfixL 2),
    op2 "xor" xor (InfixL 6),
    op1 "not" not,
    op1 "!" not,
    op1 "~" not
    ]

-- TODO: add more generic Op domain
genericOpScope :: TypedScope AnOp
genericOpScope = typedAOScope $ map (anOp :: Op Bool -> AnOp) []
  -- Op "===" [Wildcard, Wildcard] (\[a,b] -> a == b) (InfixL 6),
  -- Op "!==" [Wildcard, Wildcard] (\[a,b] -> a /= b) (InfixL 6)
  -- ]

-- maybe use TH
parseableTypes :: [APType]
parseableTypes = [pType @Double, pType @Bool]

fullDefaultScope :: Scope AParseable
fullDefaultScope = mconcat $ map getDefaultScope parseableTypes where
  getDefaultScope :: APType -> Scope AParseable
  getDefaultScope (APType t) = getDefaultScope' t
  getDefaultScope' :: forall x. Parseable x => Proxy x -> Scope AParseable
  getDefaultScope' _ = AParseable <$> defaultScope @x

fullOpScope :: TypedScope AnOp
fullOpScope = genericOpScope `mappend` foldMap (\(APType t) -> opsOf t) parseableTypes where
  opsOf :: Parseable x => Proxy x -> TypedScope AnOp
  opsOf p = defaultOpScope p `mappend` opScope p
