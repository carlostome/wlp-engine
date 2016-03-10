{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
module Expr (
  -- * Expression type
  Expr,
  -- * Smart constructors
  l, vi, vb,
  ati,  atb,
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
  subst1, subst2, boundVars
  ) where

import           Data.List                    (delete, nub)
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.SBV                     hiding (forall, (==>), (<+>))
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
  IxBArr  :: Name -> Expr Integer -> Expr Bool

  BinOp   :: (C a, C b) => BinOp a b -> Expr a -> Expr a -> Expr b
  UnOp    :: UnOp a    -> Expr a -> Expr a
  Forall  :: Var -> Expr Bool -> Expr Bool

-- Smart constructors
l :: C t => t -> Expr t
l   = Lit
vi  = VarI
vb  = VarB
ati = IxIArr
atb = IxBArr
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
    IxBArr name ix -> do
      sym1 <- interpret envI envB envAI envAB ix
      case M.lookup name envAB of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type [bool]"
        Just arr    -> return (readArray arr sym1)

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

freeVars :: Expr t -> [Var]
freeVars expr = case expr of
  Lit    _   -> []
  VarI n   -> [n ::: int]
  VarB n  -> [n ::: bool]
  Forall var e -> var `delete` freeVars e
  IxIArr n ix -> [n ::: intarr] ++ freeVars ix
  IxBArr n ix -> [n ::: boolarr] ++ freeVars ix
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
    IxBArr _ ix -> e

subst2 :: Map Name (Expr Integer) -> Expr a -> Expr a
subst2 map_ e =
  case e of
    VarI name -> M.findWithDefault e name map_
    BinOp op e1 e2 -> BinOp op (subst2 map_ e1) (subst2 map_ e2)
    UnOp op e1     -> UnOp  op (subst2 map_ e1)
    Forall var e   -> Forall var (subst2 map_ e)
    Lit b          -> e
    IxIArr name ix  -> IxIArr name (subst2 map_ ix)
    IxBArr name ix -> e

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance Pretty t => Pretty (Expr t) where
  pretty (Lit n)     = pretty n
  pretty (VarI n)  = text n
  pretty (VarB n) = text n
  pretty (IxIArr n ix)  = hcat [text n, brackets (pretty ix)]
  pretty (IxBArr n ix) = hcat [text n, brackets (pretty ix)]
  pretty (Forall var e)   = hsep [text "forall ", pretty var] <> char '.' <+> pretty e
  pretty (UnOp  op  e1)   = hcat [pretty op, pretty e1]
  pretty (BinOp op e1 e2) = parens (hcat [pretty e1, pretty op,  pretty e2])

instance (Pretty a, Pretty b) => Pretty (BinOp a b) where
  pretty And = text "/\\"
  pretty Or  = text "\\/"
  pretty Imply = text "==>"
  pretty Add = text "+"
  pretty Minus = text "-"
  pretty Lt = text "<"
  pretty LEq = text "<="
  pretty Eq = text "=="

instance Pretty a => Pretty (UnOp a) where
  pretty Not = char '~'

