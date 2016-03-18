{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
module Expr (
  -- * Expression type
  Expr,
  -- * Smart constructors
  l, vi, vb,
  ati,
  forall, foralls,
  -- * Operators
  -- ** Logical operators
  (/\), (\/), (==>), neg,
  -- ** Arithmetic operators
  (+.), (-.),
  -- ** Comparison operators
  (<.), (<=.), (>.), (>=.), (==.),
  -- * Interpretation
  interpret',
  -- ** Auxiliary functions
  subst1, subst2, boundVars, cond1, cond2, splice

  ) where

import           Control.Applicative          ((<|>))
import           Data.List                    (delete, nub)
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.Maybe                   (fromMaybe)
import           Data.SBV                     hiding (forall, (<+>), (==>))
import qualified Data.SBV                     as SBV
import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

import Var

type C a = (Pretty a, SymWord a)

-- | Expressions in the (typed) logic language.
data Expr t where
  Lit    :: C n => n -> Expr n
  VarI   :: Name -> Expr Integer
  VarB   :: Name -> Expr Bool

  IxIArr  :: Name -> Expr Integer -> Expr Integer
  -- IxBArr  :: Name -> Expr Integer -> Expr Bool

  BinOp   :: (C a, C b) => BinOp a b -> Expr a -> Expr a -> Expr b
  UnOp    :: UnOp a    -> Expr a -> Expr a

  Cond    :: Expr Bool -> Expr a -> Expr a -> Expr a
  Forall  :: Var -> Expr Bool -> Expr Bool

-- Smart constructors
l :: C t => t -> Expr t
l   = Lit
vi  = VarI
vb  = VarB
ati = IxIArr
-- atb = IxBArr
forall  = Forall
foralls vs expr = foldr Forall expr vs

-- | Binary Operator
data BinOp a b where
  And, Or, Imply :: BinOp Bool Bool
  Add, Minus     :: BinOp Integer Integer
  Lt, LEq, Eq    :: BinOp Integer Bool

-- | Unary operator
data UnOp a where
  Not :: UnOp Bool

(/\), (\/), (==>) :: Expr Bool -> Expr Bool -> Expr Bool
(/\)  = BinOp And
(\/)  = BinOp Or
(==>) = BinOp Imply

(+.), (-.) :: Expr Integer -> Expr Integer -> Expr Integer
(+.) = BinOp Add
(-.) = BinOp Minus

(<.), (<=.), (>.), (>=.), (==.) :: Expr Integer -> Expr Integer -> Expr Bool
(<.)    = BinOp Lt
(<=.)   = BinOp LEq
(>.) a  = UnOp Not . BinOp LEq a
(>=.) a = UnOp Not . BinOp Lt a
(==.) = BinOp Eq

neg :: Expr Bool -> Expr Bool
neg = UnOp Not

cond = Cond

infixl 6 +., -.
infixl 5 <. ,<=., ==.

infixl 4 /\
infixl 3 \/
infixl 2 ==>

interpret' :: SymWord t => Expr t -> Symbolic (SBV t)
interpret' = interpret M.empty M.empty M.empty M.empty

interpret :: SymWord t
          => Map Name SInteger
          -> Map Name SBool
          -> Map Name (SArray Integer Integer)
          -> Map Name (SArray Integer Bool)
          -> Expr t -> Symbolic (SBV t)
interpret envI envB envAI envAB expr =
  case expr of
    Lit n       -> return (literal n)
    VarI name ->
      case M.lookup name envI of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type int"
        Just val    -> return val
    VarB name ->
      case M.lookup name envB of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type int"
        Just val    -> return val

    IxIArr name ix -> do
      sym1 <- interpret envI envB envAI envAB ix
      case M.lookup name envAI of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type [int]"
        Just arr    -> return (readArray arr sym1)
    -- IxBArr name ix -> do
    --   sym1 <- interpret envI envB envAI envAB ix
    --   case M.lookup name envAB of
    --     Nothing     -> error $ "Unbound variable: " ++ name ++ " of type [bool]"
    --     Just arr    -> return (readArray arr sym1)

    Forall (var ::: type') expr ->
      case type' of
        Prim Bool -> do
         symVar <- SBV.forall var
         interpret envI (M.insert var symVar envB) envAI envAB expr
        Prim Int -> do
         symVar <- SBV.forall var
         interpret (M.insert var symVar envI) envB envAI envAB  expr
        Array Int  -> do
         symVar <- Data.SBV.newArray var Nothing
         interpret envI envB (M.insert var symVar envAI) envAB expr
        Array Bool -> do
         symVar <- Data.SBV.newArray var Nothing
         interpret envI envB envAI (M.insert var symVar envAB) expr
    BinOp op e1 e2 -> do
       sym1 <- interpret envI envB envAI envAB  e1
       sym2 <- interpret envI envB envAI envAB  e2
       return (getBinOp op sym1 sym2)
    UnOp op e1 -> do
       sym1 <- interpret envI envB envAI envAB  e1
       return (getUnOp op sym1)

  where getBinOp :: (SymWord a, SymWord b) => BinOp a b -> (SBV a -> SBV a -> SBV b)
        getBinOp And = (&&&)
        getBinOp Or  = (|||)
        getBinOp Imply = (SBV.==>)
        getBinOp Add = (+)
        getBinOp Minus = (-)
        getBinOp Lt = (.<)
        getBinOp LEq = (.<=)
        getBinOp Eq = (.==)

        getUnOp :: (SymWord a) => UnOp a -> (SBV a -> SBV a)
        getUnOp Not = bnot

splice :: (Name, Expr Integer) -> Expr Integer -> Expr t-> Expr t
splice (n,ix) expr e@(Lit q)  = e
splice (n,ix) expr e@(VarI q) = e
splice (n,ix) expr e@(VarB q) = e
splice (n,ix) expr (BinOp op q1 q2) = BinOp op (splice (n,ix) expr q1) (splice (n,ix) expr q2)
splice (n,ix) expr e@(IxIArr n' ix')
  | n == n'   = Cond (ix ==. ix') expr e
  | otherwise = e
splice (n,ix) expr (UnOp op q2)   = UnOp op $ splice (n,ix) expr q2
splice (n,ix) expr (Forall v q2) = Forall v $ splice (n,ix) expr q2

cond1 ::  Expr Bool -> Expr Bool
cond1 e@(Lit _)  = e
cond1 e@(VarB _) = e
cond1 (BinOp And e2 e3)   = cond1 e2 /\ cond1 e3
cond1 (BinOp Or e2 e3)    = cond1 e2 \/ cond1 e3
cond1 (BinOp Imply e2 e3) = cond1 e2 ==> cond1 e3
cond1 e@(BinOp Lt e2 e3)    = fromMaybe e
  (cond2 (BinOp Lt e2) e3 <|> cond2 (flip (BinOp Lt) e3) e2)
cond1 e@(BinOp LEq e2 e3)   = fromMaybe e
  (cond2 (BinOp LEq e2) e3 <|> cond2 (flip (BinOp LEq) e3) e2)
cond1 e@(BinOp Eq e2 e3)    = fromMaybe e
  (cond2 (BinOp Eq e2) e3 <|> cond2 (flip (BinOp Eq) e3) e2)
cond1 (UnOp op e)         = neg $ cond1 e
cond1 (Forall v e)        = forall v (cond1 e)

cond2 :: (Expr Integer -> Expr Bool) -> Expr Integer -> Maybe (Expr Bool)
cond2 f e@(Lit expr)  = Nothing
cond2 f e@(VarI expr) = Nothing
cond2 f e@(IxIArr name ix) = Nothing
cond2 f (BinOp Add e2 e3)  =
  cond2 (f . BinOp Add e2) e3 <|> cond2 (f . BinOp Add e3) e2
cond2 f (BinOp Minus e2 e3) =
  cond2 (f . BinOp Minus e2) e3 <|> cond2 (f . BinOp Minus e3) e2
cond2 f (Cond c e1 e2) = Just $ cond1 ((c ==> f e1) /\ (neg c ==> f e2))

freeVars :: Expr t -> [Var]
freeVars expr = case expr of
  Lit    _   -> []
  VarI n   -> [n ::: int]
  VarB n  -> [n ::: bool]
  Forall var e -> var `delete` freeVars e
  IxIArr n ix -> [n ::: intarr] ++ freeVars ix
  -- IxBArr n ix -> [n ::: boolarr] ++ freeVars ix
  UnOp _ e       -> freeVars e
  BinOp _ e1 e2  -> nub (freeVars e1 ++ freeVars e2)

boundVars :: Expr Bool -> Expr Bool
boundVars e = let vs = freeVars e in foralls vs e 

subst1 :: Map Name (Expr Bool) -> Expr a -> Expr a
subst1 map_ e =
  case e of
    VarB name -> M.findWithDefault e name map_
    BinOp op e1 e2 -> BinOp op (subst1 map_ e1) (subst1 map_ e2)
    UnOp op e1     -> UnOp  op (subst1 map_ e1)
    Forall var e   -> Forall var (subst1 map_ e)
    Lit b          -> e
    IxIArr name ix  -> IxIArr name (subst1 map_ ix)
    -- IxBArr _ ix -> e

subst2 :: Map Name (Expr Integer) -> Expr a -> Expr a
subst2 map_ e =
  case e of
    VarI name -> M.findWithDefault e name map_
    BinOp op e1 e2 -> BinOp op (subst2 map_ e1) (subst2 map_ e2)
    UnOp op e1     -> UnOp  op (subst2 map_ e1)
    Forall var e   -> Forall var (subst2 map_ e)
    Lit b          -> e
    IxIArr name ix  -> IxIArr name (subst2 map_ ix)
    -- IxBArr name ix -> e

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance Pretty t => Pretty (Expr t) where
  pretty (Lit n)     = pretty n
  pretty (VarI n)  = text n
  pretty (VarB n) = text n
  pretty (IxIArr n ix)  = hcat [text n, brackets (pretty ix)]
  -- pretty (IxBArr n ix) = hcat [text n, brackets (pretty ix)]
  pretty (Forall var e)   = hsep [text "forall ", pretty var] <> char '.' <+> pretty e
  pretty (UnOp  op  e1)   = hcat [pretty op, pretty e1]
  pretty (BinOp op e1 e2) = hcat [pretty e1, pretty op,  pretty e2]
  pretty (Cond e1 e2 e3)  = hsep [pretty e1, text "-->", pretty e2, char '|', pretty e3]

instance (Pretty a, Pretty b) => Pretty (BinOp a b) where
  pretty And = text " /\\ "
  pretty Or  = text " \\/ "
  pretty Imply = text " ==> "
  pretty Add = text "+"
  pretty Minus = text "-"
  pretty Lt = text "<"
  pretty LEq = text "<="
  pretty Eq = text "="

instance Pretty a => Pretty (UnOp a) where
  pretty Not = char '~'

