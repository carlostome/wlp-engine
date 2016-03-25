{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Expr (
  -- * Type
  BOOL, INT, Array, Prim, I, B,
  Type,
  SType, SPType,
  -- ** Smart constructors
  int, bool, intarr, boolarr,
  -- * Variable
  Var(..), Name,
  -- ** Smart constructors
  i, b, ai, ab,
  -- * Expression
  Expr,
  -- ** Smart constructors
  li, lb, v,
  vi, vb, vai, vab,
  ixi, ixb,
  forall, exists,
  -- ** Operators
  -- *** Logical operators
  (/\), (\/), (==>), (<==>), neg,
  -- *** Arithmetic operators
  (+.), (-.),
  -- *** Comparison operators
  (<.), (<=.), (>.), (>=.), (==.),
  -- * Substitution and targets
  Target, tv, tix,
  Asg, ati, atb, (.:=), subst,
  -- * Interpretation
  prove, proveBool, Result(..),
  -- * Quirky untyped version of types
  UVar(..), UTarget, UExpr,
  -- ** Constructors
  u, ut, ue,
  -- ** Utility functions
  mixexp, mixtarg,
  -- * Debug
  rn, bound, toPrenex, cond1
  ) where

import           Control.Applicative          ((<|>))
import           Data.Data
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.Maybe                   (fromMaybe)
import qualified Data.SBV                     as SBV
import           Data.Set                     (Set)
import qualified Data.Set                     as S
import           Data.Type.Equality
import           Data.Unique
import           System.IO.Unsafe
import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

--------------------------------------------------------------------------------
-- Type
--------------------------------------------------------------------------------

data Type  = Prim PType | Array PType
  deriving (Eq, Ord, Show)

data PType = I | B
  deriving (Eq, Ord, Show)

data SPType :: PType -> * where
  SI :: SPType I
  SB :: SPType B

data SType :: Type -> * where
  SPrim  :: SPType t -> SType (Prim t)
  SArray :: SPType t -> SType (Array t)

-- | Type synonyms for export
type INT  = Prim I
type BOOL = Prim B
type Array = 'Array
type Prim  = 'Prim
type I   = 'I
type B   = 'B

-- Smart Constructors
int :: SType (Prim I)
int     = SPrim SI

bool :: SType (Prim B)
bool    = SPrim SB

intarr :: SType (Array I)
intarr  = SArray SI

boolarr :: SType (Array B)
boolarr = SArray SB

-- Instances
instance TestEquality SType where
  testEquality (SPrim SI) (SPrim SI) = Just Refl
  testEquality (SPrim SB) (SPrim SB) = Just Refl
  testEquality (SArray SI) (SArray SI) = Just Refl
  testEquality (SArray SB) (SArray SB) = Just Refl
  testEquality _ _ = Nothing


--------------------------------------------------------------------------------
-- Variable
--------------------------------------------------------------------------------

-- | Type of identifier (for now string)
type Name = String

-- | Variable tagged with its "Type"
data Var :: Type -> * where
  (:::) :: Name -> SType t -> Var t

-- Smart constructors
i :: Name -> Var INT
i n = (n ::: int)
b :: Name -> Var BOOL
b n = (n ::: bool)
ai :: Name -> Var (Array I)
ai n = (n ::: intarr)
ab :: Name -> Var (Array B)
ab n = (n ::: boolarr)

-- Instances
instance Eq (Var t) where
  (v1 ::: _) == (v2 ::: _) = v1 == v2

instance Ord (Var t) where
  (v0 ::: _) `compare` (v1 ::: _) = compare v0 v1

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

-- | Typed literals
data Lit :: Type -> * where
  Int  :: Int  -> Lit INT
  Bool :: Bool -> Lit BOOL

-- | Expressions in the (typed) logic language.
data Expr :: Type -> * where
  Lit   :: Lit t -> Expr t
  Var   :: Var t -> Expr t

  Ix    :: Expr (Array t) -> Expr INT -> Expr (Prim t)

  BinOp   :: BinOp a b -> Expr a -> Expr a -> Expr b
  UnOp    :: UnOp a    -> Expr a -> Expr a

  Cond    :: Expr BOOL -> Expr a -> Expr a -> Expr a

  Quant    :: Quantifier -> Var s -> Expr BOOL -> Expr BOOL

-- | Binary operations
data BinOp :: Type -> Type -> * where
  Plus  :: BinOp INT INT
  Minus :: BinOp INT INT

  Eq   :: BinOp INT BOOL
  LEq  :: BinOp INT BOOL
  Lt   :: BinOp INT BOOL
  Gt   :: BinOp INT BOOL
  GEq  :: BinOp INT BOOL

  Imply   :: BinOp BOOL BOOL
  Equiv   :: BinOp BOOL BOOL
  And  :: BinOp BOOL BOOL
  Or   :: BinOp BOOL BOOL


data UnOp :: Type -> * where
  Not :: UnOp BOOL

data Quantifier = Forall | Exists

-- | Smart constructors

-- Literals
li :: Int -> Expr INT
li = Lit . Int

lb :: Bool -> Expr BOOL
lb = Lit . Bool

v :: Var t -> Expr t
v  = Var
vi :: Name -> Expr INT
vi = v . i
vb :: Name -> Expr BOOL
vb = v . b
vai :: Name -> Expr (Array I)
vai = v . ai
vab :: Name -> Expr (Array B)
vab = v . ab

ixi :: Name -> Expr INT -> Expr INT
n `ixi` x = Ix (Var (n ::: intarr)) x

ixb :: Name -> Expr INT -> Expr BOOL
n `ixb` x = Ix (Var (n ::: boolarr)) x

-- | Boolean operators
(/\), (\/),(==>), (<==>) :: Expr BOOL -> Expr BOOL -> Expr BOOL
(/\)  = BinOp And
(\/)  = BinOp Or
(==>)   = BinOp Imply
(<==>)  = BinOp Equiv

neg :: Expr BOOL -> Expr BOOL
neg   = UnOp Not

infixl 4 /\
infixl 3 \/
infixl 2 ==>, <==>

-- | Arithmetic operators
(+.), (-.) :: Expr INT -> Expr INT -> Expr INT
(+.) = BinOp Plus
(-.) = BinOp Minus

infixl 6 +., -.

-- | Comparison operators (only between INT)
(<.), (<=.), (>.), (>=.), (==.) :: Expr INT -> Expr INT -> Expr BOOL
(<.)  = BinOp Lt
(<=.) = BinOp LEq
(>.)  = BinOp Gt
(>=.) = BinOp GEq
(==.) = BinOp Eq

infixl 5 <. ,<=., ==., >., >=.

-- | Quantification shorhand
forall, exists :: Var t -> Expr BOOL -> Expr BOOL
forall = Quant Forall
exists = Quant Exists

-- | Target of substitutions
data Target :: Type -> * where
  TVar :: Var t -> Target t
  TArr :: Var (Array t) -> Expr INT -> Target (Prim t)

tv :: Var t -> Target t
tv   = TVar

tix :: Var (Array t) -> Expr INT -> Target (Prim t)
tix  = TArr

-- | An assignment is a pair of a target and
-- an expression of the same type.
data Asg :: * where
  Asg :: Target t -> Expr t -> Asg

(.:=) :: Var t -> Expr t -> Asg
v' .:= e      = Asg (TVar v') e

infixl 1 .:=

ati :: Name -> Expr INT -> Expr INT -> Asg
ati n ix     = Asg (TArr (n ::: intarr) ix)

atb :: Name -> Expr INT -> Expr BOOL -> Asg
atb n ix     = Asg (TArr (n ::: boolarr) ix)

assg :: [Asg] ->
        ( Map (Var INT)  (Expr INT)
        , Map (Var BOOL) (Expr BOOL)
        , Map (Var (Array I)) (Either (Expr (Array I)) (Expr INT, Expr INT))
        , Map (Var (Array B)) (Either (Expr (Array B)) (Expr INT, Expr BOOL)))
assg [] = (M.empty, M.empty, M.empty, M.empty)
assg ((Asg tgt ex) : xs) =
  let (mi, mb, mai, mab) = assg xs
  in case tgt of
      (TVar v'@(_ ::: (SPrim SI)))  -> (M.insert v' ex mi, mb, mai, mab)
      (TVar v'@(_ ::: (SPrim SB)))  -> (mi, M.insert v' ex mb, mai, mab)
      (TVar v'@(_ ::: (SArray SI))) -> (mi, mb, M.insert v' (Left ex) mai, mab)
      (TVar v'@(_ ::: (SArray SB))) -> (mi, mb, mai, M.insert v' (Left ex) mab)
      (TArr v'@(_ ::: (SArray SI)) ix) -> (mi, mb, M.insert v' (Right (ix,ex)) mai, mab)
      (TArr v'@(_ ::: (SArray SB)) ix) -> (mi, mb, mai, M.insert v' (Right (ix,ex)) mab)

-- | Given a list of assignments perform substitution
-- over an expression.
subst :: [Asg] -> Expr BOOL -> Expr BOOL
subst as ex = cond1 $ subst' (assg as) ex

-- | Get all free variables of an expression.
free :: Expr t -> (Set (Var INT), Set (Var BOOL), Set (Var (Array I)), Set (Var (Array B)))
free e = case e of
  Lit _           -> (S.empty, S.empty, S.empty, S.empty)
  Var v'@(_ ::: t) ->
    case t of
      SPrim SI  -> (S.singleton v', S.empty, S.empty, S.empty)
      SPrim SB  -> (S.empty, S.singleton v', S.empty, S.empty)
      SArray SI -> (S.empty, S.empty, S.singleton v', S.empty)
      SArray SB -> (S.empty, S.empty, S.empty, S.singleton v')
  Ix (Var v'@(_ ::: t)) ix ->
    let (fi, fb, fai, fab)     = free ix
    in case t of
        SArray SI -> (fi, fb, S.insert v' fai, fab)
        SArray SB -> (fi, fb, fai, S.insert v' fab)
  BinOp _ e1 e2 ->
    let (fi, fb, fai, fab)     = free e1
        (fi', fb', fai', fab') = free e2
    in  (fi `S.union` fi', fb `S.union` fb',fai `S.union` fai',fab `S.union` fab')
  UnOp _ e1 -> free e1
  Quant _ v'@(_ ::: t) e1 ->
    let (fi, fb, fai, fab)     = free e1
    in case t of
        SPrim SI  -> (S.delete v' fi, fb, fai, fab)
        SPrim SB  -> (fi, S.delete v' fb, fai, fab)
        SArray SI -> (fi, fb, S.delete v' fai, fab)
        SArray SB -> (fi, fb, fai, S.delete v' fab)
  Cond _ _ _ -> error "PANIC! Cond constructor found (free)."

-- | Remove a Cond constructor from a BOOL expr
cond1 ::  Expr BOOL -> Expr BOOL
cond1 e@(Lit _)  = e
cond1 e@(Var _)  = e
cond1 (BinOp Imply e2 e3)   = cond1 e2 ==> cond1 e3
cond1 (BinOp Equiv e2 e3)   = cond1 e2 ==> cond1 e3
cond1 (BinOp And e2 e3)   = cond1 e2 /\ cond1 e3
cond1 e@(BinOp Gt e2 e3)    = fromMaybe e
  (cond2 (BinOp Gt e2) e3 <|> cond2 (flip (BinOp Gt) e3) e2)
cond1 e@(BinOp GEq e2 e3)   = fromMaybe e
  (cond2 (BinOp GEq e2) e3 <|> cond2 (flip (BinOp GEq) e3) e2)
cond1 (BinOp Or e2 e3)    = cond1 e2 \/ cond1 e3
cond1 e@(BinOp Lt e2 e3)    = fromMaybe e
  (cond2 (BinOp Lt e2) e3 <|> cond2 (flip (BinOp Lt) e3) e2)
cond1 e@(BinOp LEq e2 e3)   = fromMaybe e
  (cond2 (BinOp LEq e2) e3 <|> cond2 (flip (BinOp LEq) e3) e2)
cond1 e@(BinOp Eq e2 e3)    = fromMaybe e
  (cond2 (BinOp Eq e2) e3 <|> cond2 (flip (BinOp Eq) e3) e2)
cond1 (UnOp op e)           = UnOp op $ cond1 e
cond1 (Quant q v' e)        = Quant q v' (cond1 e)

cond2 :: (Expr INT -> Expr BOOL) -> Expr INT -> Maybe (Expr BOOL)
cond2 _ (Lit _) = Nothing
cond2 _ (Var _) = Nothing
cond2 _ (Ix _ _) = Nothing
cond2 f (BinOp Plus e2 e3)  =
  cond2 (f . BinOp Plus e2) e3 <|> cond2 (f . BinOp Plus e3) e2
cond2 f (BinOp Minus e2 e3) =
  cond2 (f . BinOp Minus e2) e3 <|> cond2 (f . BinOp Minus e3) e2
cond2 f (Cond c e1 e2) = Just $ cond1 ((c ==> f e1) /\ (neg c ==> f e2))

type family Interpret (a :: Type) where
  Interpret (Prim I)  = SBV.SInteger
  Interpret (Prim B)  = SBV.SBool
  Interpret (Array B) = SBV.SArray Integer Bool
  Interpret (Array I) = SBV.SArray Integer Integer

-- | Interpret a boolean expression with SBV.
interpret :: Expr t -> SBV.Symbolic (Interpret t)
interpret = interpret' M.empty M.empty M.empty M.empty

interpret' :: Map Name SBV.SInteger
          -> Map Name SBV.SBool
          -> Map Name (SBV.SArray Integer Integer)
          -> Map Name (SBV.SArray Integer Bool)
          -> Expr t -> SBV.Symbolic (Interpret t)
interpret' ei eb eai eab expr =
  case expr of
    Lit l ->
      case l of
       Int  n -> return (SBV.literal (fromIntegral n))
       Bool n -> return (SBV.literal n)
    Var (n ::: t) ->
      case t of
        SPrim SI  -> return $ M.findWithDefault (error "Unbound") n ei
        SPrim SB  -> return $ M.findWithDefault (error "Unbound") n eb
        SArray SI -> return $ M.findWithDefault (error "Unbound") n eai
        SArray SB -> return $ M.findWithDefault (error "Unbound") n eab
    Ix (Var (n ::: t)) ix' -> do
      symix  <- interpret' ei eb eai eab ix'
      case t of
        SArray SI -> let arr = M.findWithDefault (error "Unbound") n eai
                     in return (SBV.readArray arr symix)
        SArray SB -> let arr = M.findWithDefault (error "Unbound") n eab
                     in return (SBV.readArray arr symix)
    BinOp op e1 e2 -> do
       sym1 <- interpret' ei eb eai eab  e1
       sym2 <- interpret' ei eb eai eab  e2
       return (getBinOp op sym1 sym2)
    UnOp op e1 -> do
       sym1 <- interpret' ei eb eai eab  e1
       return (getUnOp op sym1)
    Quant q (n ::: t) e ->
      case t of
        SPrim SI  -> do
          symVar  <- getQuant q n
          interpret' (M.insert n symVar ei) eb eai eab e
        SPrim SB  -> do
          symVar  <- getQuant q n
          interpret' ei (M.insert n symVar eb) eai eab e
        SArray SI  -> do
          symVar  <- SBV.newArray n Nothing
          interpret' ei eb (M.insert n symVar eai) eab e
        SArray SB  -> do
          symVar  <- SBV.newArray n Nothing
          interpret'  ei eb eai (M.insert n symVar eab) e
    Cond _ _ _ -> error "Cond not expected"

  where getBinOp :: BinOp a b -> (Interpret a -> Interpret a -> Interpret b)
        getBinOp Equiv = (SBV.<=>)
        getBinOp Imply = (SBV.==>)
        getBinOp And = (SBV.&&&)
        getBinOp Or  = (SBV.|||)
        getBinOp Plus  = (+)
        getBinOp Minus = (-)
        getBinOp Lt  = (SBV..<)
        getBinOp LEq = (SBV..<=)
        getBinOp Gt  = (SBV..>)
        getBinOp GEq = (SBV..>=)
        getBinOp Eq  = (SBV..==)

        getUnOp :: UnOp a -> (Interpret a -> Interpret a)
        getUnOp Not = SBV.bnot

        getQuant Forall = SBV.forall
        getQuant Exists = SBV.exists

-- | Perform substitution
subst' :: ( Map (Var INT)  (Expr INT)
         , Map (Var BOOL) (Expr BOOL)
         , Map (Var (Array I)) (Either (Expr (Array I)) (Expr INT, Expr INT))
         , Map (Var (Array B)) (Either (Expr (Array B)) (Expr INT, Expr BOOL)))
      -> Expr t -> Expr t
subst' _ (Lit s) = Lit s
subst' (mi, mb, mai, mab) e@(Var v'@(_ ::: t)) =
  case t of
    SPrim SI  -> M.findWithDefault e v' mi
    SPrim SB  -> M.findWithDefault e v' mb
    SArray SI ->
      case M.lookup v' mai of
        Just (Left v'') -> v''
        _             -> e
    SArray SB ->
      case M.lookup v' mab of
        Just (Left v'') -> v''
        _              -> e
subst' m@(_, _, mai, mab) ex@(Ix (Var v'@(_ ::: t)) e)  =
  case t of
    (SArray SI) ->
      case M.lookup v' mai of
        Just (Right (ix, newv)) -> Cond (e ==. ix) newv ex
        Just (Left v'')         -> Ix v'' (subst' m e)
        Nothing                 -> Ix (Var v') (subst' m e)
    (SArray SB) ->
      case M.lookup v' mab of
        Just (Right (ix, newv'x)) -> Cond (e ==. ix) newv'x ex
        Just (Left v'')           -> Ix v'' (subst' m e)
        Nothing                   -> Ix (Var v') (subst' m e)
subst' m (BinOp op e1 e2) = BinOp op (subst' m e1) (subst' m e2)
subst' m (UnOp op e1)     = UnOp  op (subst' m e1)
subst' m (Cond e1 e2 e3)  = Cond  (subst' m e1) (subst' m e2) (subst' m e3)
subst' (mi, mb, mai, mab) (Quant q v'@(_ ::: t) e) =
  case t of
    SPrim SI  -> Quant q v' (subst' (v' `M.delete` mi, mb , mai, mab) e)
    SPrim SB  -> Quant q v' (subst' (mi, v' `M.delete` mb , mai, mab) e)
    SArray SI -> Quant q v' (subst' (mi, mb, v' `M.delete` mai , mab) e)
    SArray SB -> Quant q v' (subst' (mi, mb, mai, v' `M.delete` mab) e)
subst' m _ = error (show m)

-- | Rename all the variables so they are unique regarding the quantifiers
--   The input to this function should not contain free variables.
--   This function must be called before transforming to prenex.
rn :: Expr t -> Expr t
rn = rn' (M.empty, M.empty, M.empty, M.empty)

rn' :: ( Map (Var INT) (Expr INT)
      , Map (Var BOOL) (Expr BOOL)
      , Map (Var (Array I)) (Expr (Array I))
      , Map (Var (Array B)) (Expr (Array B)))
      -> Expr t -> Expr t
rn' _ (Lit s) = Lit s
rn' (mi, mb, mai, mab) (Var v'@(_ ::: t)) =
  case t of
    SPrim SI  -> M.findWithDefault (error "Unbound") v' mi
    SPrim SB  -> M.findWithDefault (error "Unbound") v' mb
    SArray SI -> M.findWithDefault (error "Unbound") v' mai
    SArray SB -> M.findWithDefault (error "Unbound") v' mab
rn' m (Ix v' e)  = Ix (rn' m v') (rn' m e)
rn' m (BinOp op e1 e2) = BinOp op (rn' m e1) (rn' m e2)
rn' m (UnOp op e1)     = UnOp  op (rn' m e1)
rn' m (Cond e1 e2 e3)  = Cond  (rn' m e1) (rn' m e2) (rn' m e3)
rn' (mi, mb, mai, mab) (Quant q v'@(n ::: t) e) =
  let uniq = hashUnique $ unsafePerformIO newUnique
      newn = concat [n,"_",show uniq]
  in case t of
      SPrim SI  -> Quant q (newn ::: t) (rn' (M.insert v' (Var (newn :::t)) mi, mb , mai, mab) e)
      SPrim SB  -> Quant q (newn ::: t) (rn' (mi, M.insert v' (Var (newn :::t)) mb , mai, mab) e)
      SArray SI -> Quant q (newn ::: t) (rn' (mi, mb, M.insert v' (Var (newn :::t)) mai, mab) e)
      SArray SB -> Quant q (newn ::: t) (rn' (mi, mb, mai, M.insert v' (Var (newn :::t)) mab) e)

-- | Bound all free variables in the expression.
bound :: Expr BOOL -> Expr BOOL
bound e =
  let (si, sb, sai, sab) = free e
  in    foldl (flip forall)
          (foldl (flip forall)
            (foldl (flip forall)
              (foldl (flip forall) e si) sb) sai) sab

--------------------------------------------------------------------------------
-- Rules for prenex conversion

-- Simplification rules
simplify :: Expr BOOL -> (Maybe (Expr BOOL))
-- double negation
simplify (UnOp Not (UnOp Not e)) = Just e
-- de Morgan
simplify (UnOp Not (BinOp And e1 e2)) =
  Just $ BinOp Or (UnOp Not e1) (UnOp Not e2)
simplify (UnOp Not (BinOp Or e1 e2))  =
  Just $ BinOp And (UnOp Not e1) (UnOp Not e2)
-- negation on quantifier
simplify (UnOp Not (Quant q v' e))  =
  Just $ Quant (flip_ q) v' (UnOp Not e)
  where flip_ Forall = Exists
        flip_ Exists = Forall
-- Quantifier ov'er conectiv'es
simplify (BinOp And (Quant q v' e) p) =
  Just $ Quant q v' (BinOp And e p)
simplify (BinOp And p (Quant q v' e)) =
  Just $ Quant q v' (BinOp And p e)
simplify (BinOp Or  (Quant q v' e) p) =
  Just $ Quant q v' (BinOp Or e p)
simplify (BinOp Or  p (Quant q v' e)) =
  Just $ Quant q v' (BinOp Or p e)
-- Implication removal
simplify (BinOp Imply e2 e3) =
-- Equivalence removal
  Just $ BinOp Or (UnOp Not e2) e3
simplify (BinOp Equiv e2 e3) =
  Just $ BinOp And
    (BinOp Or (UnOp Not e2) e3) (BinOp Or (UnOp Not e3) e2)
simplify (Lit _) = Nothing
simplify (Var _) = Nothing
simplify (Ix _ _) = Nothing
simplify (BinOp And e1 e2) = do
  let (e1', e2') = (simplify e1, simplify e2)
  case (e1',e2') of
    (Nothing,Nothing) -> Nothing
    (Nothing,Just e2'') -> Just $ BinOp And e1 e2''
    (Just e1'',_ )      -> Just $ BinOp And e1'' e2
simplify (BinOp Or e1 e2) = do
  let (e1', e2') = (simplify e1, simplify e2)
  case (e1',e2') of
    (Nothing,Nothing)   -> Nothing
    (Nothing,Just e2'') -> Just $ BinOp Or e1 e2''
    (Just e1'',_) -> Just $ BinOp Or e1'' e2
simplify (UnOp Not e)  = fmap (UnOp Not) (simplify e)
simplify (Quant q v' e) = fmap (Quant q v') (simplify e)
simplify _ = Nothing

-- | Transform a boolean expression into its prenex
-- equivalent form.
toPrenex :: Expr BOOL -> Expr BOOL
toPrenex e = app simplify (e, Just e)
  where
    app _ (a,Nothing) = a
    app f (_,Just a)  = app f (a, f a)

--------------------------------------------------------------------------------
-- Interpretation of Expr with SBV
--------------------------------------------------------------------------------

-- | Type of results
data Result = Valid | NotValid Doc

-- | Prove the validity of a boolean expression.
proveBool :: Expr BOOL -> Bool
proveBool = isValid . toResult . unsafePerformIO
          . SBV.prove . interpret . toPrenex . rn . bound

-- | Prove the validity with explicit counter example.
prove :: Expr BOOL -> Result
prove = toResult . unsafePerformIO
        . SBV.prove . interpret . toPrenex . rn . bound

isValid :: Result -> Bool
isValid Valid        = True
isValid (NotValid _) = False

toResult :: SBV.ThmResult -> Result
toResult (SBV.ThmResult (SBV.Unsatisfiable _))   = Valid
toResult s@(SBV.ThmResult (SBV.Satisfiable _ _)) = NotValid (text . show $ s)
toResult (SBV.ThmResult _)                       = NotValid (text "SBV unable to prove for unknown reason.")

--------------------------------------------------------------------------------
-- Untyped version of types
--------------------------------------------------------------------------------

-- | Untyped variable
data UVar where
  UV :: SType t -> Var t    -> UVar

u :: Var t -> UVar
u (n ::: t) = UV t (n ::: t)

-- | Untyped target
data UTarget where
  UT :: SType t -> Target t -> UTarget

ut :: Target t -> UTarget
ut t@(TVar (__ ::: t2))    = UT t2 t
ut t@(TArr (__ ::: (SArray SI)) _) = UT int  t
ut t@(TArr (__ ::: (SArray SB)) _) = UT bool t

-- | Untyped expression
data UExpr where
  UE :: SType t -> Expr t -> UExpr

ue :: Expr t -> UExpr
ue e@(Lit (Int _))  = UE int  e
ue e@(Lit (Bool _)) = UE bool e
ue e@(Var (_ ::: t)) = UE t e
ue e@(Ix (Var (_ ::: (SArray SI))) _) = UE int e
ue e@(Ix (Var (_ ::: (SArray SB))) _) = UE bool e
ue e@(BinOp Plus _ _)  = UE int e
ue e@(BinOp Minus _ _) = UE int e
ue e@(BinOp Eq _ _) = UE bool e
ue e@(BinOp LEq _ _) = UE bool e
ue e@(BinOp Lt _ _) = UE bool e
ue e@(BinOp GEq _ _) = UE bool e
ue e@(BinOp Gt _ _) = UE bool e
ue e@(BinOp Imply _ _) = UE bool e
ue e@(BinOp Equiv _ _) = UE bool e
ue e@(BinOp And _ _) = UE bool e
ue e@(BinOp Or _ _) = UE bool e
ue e@(UnOp Not _) = UE bool e
ue e@(Quant _ _ _) = UE bool e

-- | Given an untyped var and and untyped expression
-- return an assignment if their type match.
mixexp :: UVar -> UExpr -> Maybe Asg
mixexp (UV (SPrim SI) v') (UE (SPrim SI) e) = Just $ Asg (TVar v') e
mixexp (UV (SPrim SB) v') (UE (SPrim SB) e) = Just $ Asg (TVar v') e
mixexp (UV (SArray SI) v') (UE (SArray SI) e) = Just $ Asg (TVar v') e
mixexp (UV (SArray SB) v') (UE (SArray SB) e) = Just $ Asg (TVar v') e
mixexp _ _ = Nothing

-- | Given an untyped var and and untyped target
-- return an assignment if their type match.
mixtarg :: UTarget -> UVar -> Maybe Asg
mixtarg (UT (SPrim SI) t') (UV (SPrim SI) e) = Just $ Asg t' (Var e)
mixtarg (UT (SPrim SB) t') (UV (SPrim SB) e) = Just $ Asg t' (Var e)
mixtarg (UT (SArray SI) t') (UV (SArray SI) e) = Just $ Asg t' (Var e)
mixtarg (UT (SArray SB) t') (UV (SArray SB) e) = Just $ Asg t' (Var e)


----------------------------------------------------------------------------------
-- Pretty printing and Show instances
----------------------------------------------------------------------------------

instance Show (SPType t) where
  show SI = "int"
  show SB = "bool"

instance Show (SType t) where
  show (SPrim e) = show e
  show (SArray e) = concat ["[", show e, "]"]

instance Pretty (SType t) where
  pretty t = text (show t)

instance Show (Var t) where
  show (n ::: _) = {- takeWhile (/='_') -} n

instance Pretty (Var t) where
  pretty (name ::: type') = hcat [ text $ takeWhile (/='_') name, text ":", pretty type']

instance Show (Lit t) where
  show (Int e)  = show e
  show (Bool e) = show e

instance Pretty (Lit t) where
  pretty (Int l)  = pretty l
  pretty (Bool l) = pretty l

instance Pretty (Expr t) where
  pretty (Lit n)     = pretty n
  pretty (Var v')     = text (show v')
  pretty (Ix (Var v') ix)  = hcat [text (show v'), brackets (pretty ix)]
  pretty (Quant q v' e)   = hsep [pretty q , pretty v'] <> char '.' <+> pretty e
  pretty (UnOp  op  e1)   = hcat [pretty op, pretty e1]
  pretty (BinOp op e1 e2) = parens $ hcat [pretty e1, pretty op,  pretty e2]
  pretty (Cond e1 e2 e3)  = hsep [pretty e1, text "-->", pretty e2, char '|', pretty e3]

instance Pretty Asg where
  pretty (Asg v' t) = hsep [ pretty v', text ":="
                           , pretty t]

instance Pretty (Target t) where
  pretty (TVar t)     = text . show $ t
  pretty (TArr t1 t2) = hcat [text . show $ t1, brackets (pretty t2)]

instance Pretty (BinOp a b) where
  pretty And = text " /\\ "
  pretty Or  = text " \\/ "
  pretty Imply = text " ==> "
  pretty Plus = text "+"
  pretty Minus = text "-"
  pretty Lt = text "<"
  pretty LEq = text "<="
  pretty Gt = text ">"
  pretty GEq = text ">="
  pretty Eq = text "="

instance Pretty (UnOp a) where
  pretty Not = char '~'

instance Pretty Quantifier where
  pretty Forall = text "forall"
  pretty Exists = text "exists"

instance Show (Expr t) where
  show (Lit e) = show e
  show (Var e) = show e
  show (Ix e1 e2) = concat [show e1, "[", show e2, "]"]
  show (BinOp op e2 e3) = concat ["(", show e2, show op,  show e3, ")"]
  show (UnOp op e)      = show op ++ show e
  show (Cond c e2 e3)   = concat [show c, " -> ", show e2, "|", show e3]
  show (Quant q v' e3) = concat [show q, " ", show v', ". ", show e3]

instance Show Quantifier where
  show Forall = "forall"
  show Exists = "exists"

instance Show (BinOp t s) where
  show Plus  = "+"
  show Minus = "-"
  show Eq    = "="
  show LEq   = "<="
  show Lt    = "<"
  show GEq   = ">="
  show Gt    = ">"
  show And   = "/\\"
  show Or    = "\\/"
  show Imply = "==>"
  show Equiv = "<==>"

instance Show (UnOp t) where
  show Not = "~"

instance Pretty Result where
  pretty Valid          = text "Q.E.D"
  pretty (NotValid err) = err

instance Pretty UVar where
  pretty (UV _ v') = pretty v'

instance Pretty UTarget where
  pretty (UT _ e2) = pretty e2

instance Pretty UExpr where
  pretty (UE _ e2) = pretty e2
