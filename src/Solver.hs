{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
module Solver where

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.SBV hiding (forall)
import qualified Data.SBV as SBV
import           Data.List

-- | Statement type
data Stmt
  = Skip
  | Assert (Expr Bool)
  | Assume (Expr Bool)
  | AsgB [Name] [Expr Bool]
  | AsgI [Name] [Expr Integer]
  | AsgAI [Name] [Expr Integer]
  | AsgAB [Name] [Expr Integer]
  | Seq Stmt Stmt
  | Choice Stmt Stmt
  | While (Expr Bool) (Expr Bool) Stmt
  | Scope [Var] Stmt

-- Smart constructors
skip = Skip
assert = Assert
assume = Assume
asgb  = AsgB
asgi  = AsgI
while = While
stmts :: [Stmt] -> Stmt
stmts  = foldr Seq Skip
vars vs = Scope vs . foldr Seq Skip
choice :: [Stmt] -> Stmt
choice = foldr1 Choice

type C a = (Show a, SymWord a)

-- | Expressions in the logic language.
data Expr t where
  Lit       :: n -> Expr n
  VarInt    :: Name -> Expr Integer
  VarBool   :: Name -> Expr Bool

  IxIntArr    :: Name -> Expr Integer -> Expr Integer
  IxBoolArr   :: Name -> Expr Integer -> Expr Bool

  Forall    :: Var -> Expr Bool -> Expr Bool

  UnOp      :: (C a)      => UnOp a    -> Expr a -> Expr a
  BinOp     :: (C a, C b) => BinOp a b -> Expr a -> Expr a -> Expr b

-- Smart constructors
l  = Lit
vi = VarInt
vb = VarBool
ai = IxIntArr
ab = IxBoolArr
forall  = Forall
foralls :: [Var] -> Expr Bool -> Expr Bool
foralls vs expr = foldr Forall expr vs
t  = l True
f  = l False

(+:) = BinOp (:+:)
(-:) = BinOp (:-:)

(<:) :: (Show a, SymWord a) => Expr a -> Expr a -> Expr Bool
(<:) = BinOp (:<:)
(<=:) :: (Show a, SymWord a) => Expr a -> Expr a -> Expr Bool
(<=:)= BinOp (:<=:)
(=:=) = BinOp (:=:)

(/\:) = BinOp (:/\:)
(\/:) = BinOp (:\/:)
(==>:) = BinOp (:==>:)

infixl 6 +:, -:
infixl 5 <: ,<=:, =:=

infixl 4 /\:
infixl 3 \/:
infixl 2 ==>:

(|:) = undefined 

neg = UnOp (:!:)

data UnOp a where
  (:!:) :: UnOp Bool

instance Show a => Show (UnOp a) where
  show (:!:) = "~"

data BinOp a b where
  (:+:)  :: BinOp Integer Integer
  (:-:)  :: BinOp Integer Integer

  (:<:)  :: BinOp t Bool
  (:<=:) :: BinOp t Bool
  (:=:)  :: BinOp t Bool

  (:\/:) :: BinOp Bool Bool
  (:/\:) :: BinOp Bool Bool
  (:==>:)  :: BinOp Bool Bool

instance (Show a, Show b) => Show (BinOp a b) where
  show bop =
    case bop of
      (:+:) -> "+"
      (:-:) -> "-"

      (:<:) -> "<"
      (:<=:)-> "<="
      (:=:) -> "="

      (:\/:)-> "\\/"
      (:/\:)-> "/\\"
      (:==>:) -> "==>"

instance Show t => Show (Expr t) where
  show (Lit n)    = show n
  show (VarInt n)  = n
  show (VarBool n) = n
  show (Forall var expr)  = "forall " ++ show var ++ ". " ++ show expr
  show (BinOp  op  e1 e2) = "(" ++ show e1 ++ " " ++ show op ++ " " ++ show e2 ++ ")"
  show (UnOp   op  e1)    = show op ++ show e1

data Var = Name ::: Type

instance Eq Var where
  n1 ::: _ == n2 ::: _ = n1 == n2

instance Show Var where
  show (name ::: type') = name ++ ":" ++ show type'

data Type = Prim PrimitiveType | Array PrimitiveType
int :: Type
int = Prim Int

bool :: Type
bool = Prim Bool

intarr :: Type
intarr = Array Int

boolarr :: Type
boolarr = Array Bool

instance Show Type where
  show (Prim t)  = show t
  show (Array t) = "[" ++ show t ++ "]"

data PrimitiveType = Int | Bool

instance Show PrimitiveType where
  show Int  = "int"
  show Bool = "bool"

type Name = String

interpret :: SymWord t
          => Map Name SInteger
          -> Map Name SBool
          -> Map Name (SArray Integer Integer)
          -> Map Name (SArray Integer Bool)
          -> Expr t -> Symbolic (SBV t)
interpret envI envB envAI envAB expr =
  case expr of
    Lit n       -> return (literal n)
    VarInt name ->
      case M.lookup name envI of
        Nothing     -> error $ "Unbound variable of type int: " ++ name ++ " of type int"
        Just val    -> return val
    VarBool name ->
      case M.lookup name envB of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type int"
        Just val    -> return val
    IxIntArr name ix -> do
      sym1 <- interpret envI envB envAI envAB  e1
      case M.lookup name envB of
        Nothing     -> error $ "Unbound variable: " ++ name ++ " of type int"
        Just val    -> return val

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

getBinOp :: (SymWord a, SymWord b) => BinOp a b -> (SBV a -> SBV a -> SBV b)
getBinOp op =
  case op of
    (:+:) -> (+)
    (:-:) -> (-)

    (:<:) -> (.<)
    (:<=:)-> (.<=)
    (:=:) -> (.==)

    (:\/:) -> (|||)
    (:/\:) -> (&&&)
    (:==>:) -> (==>)

getUnOp :: UnOp a -> (SBV a -> SBV a)
getUnOp op =
  case op of
    (:!:) -> bnot

wlp :: Stmt
    -> Expr Bool
    -> Expr Bool
wlp stmt q =
  case stmt of
    Skip -> q
    Assert p -> p /\:  q
    Assume p -> p ==>: q
    AsgB vars exprs -> subst1 (M.fromList $ zip vars exprs) q
    AsgI vars exprs -> subst2 (M.fromList $ zip vars exprs) q
    Seq s1 s2 -> wlp s1 (wlp s2 q)
    Choice s1 s2 -> wlp s1 q /\: wlp s2 q
    While inv cond s ->
      let invcheck = inv /\: cond ==>: wlp s inv
      in  foralls (getVars invcheck) invcheck /\:
          ((inv /\: neg cond) ==>: q) /\:
          ((inv /\: cond)     ==>: wlp s inv)
    Scope vs s -> foldr Forall (wlp s q) vs

getVars :: Expr t -> [Var]
getVars expr = case expr of
  Lit    _   -> []
  VarInt n   -> [n ::: int]
  VarBool n  -> [n ::: bool]
  ArrInt  n i -> undefined
  ArrBool n i -> undefined
  Forall _ _ -> []
  UnOp _ e       -> getVars e
  BinOp _ e1 e2  -> nub (getVars e1 ++ getVars e2)

check stmt = prove $ interpret M.empty M.empty M.empty M.empty (wlp stmt (Lit true))

subst1 :: Map Name (Expr Bool) -> Expr a -> Expr a
subst1 map_ e =
  case e of
    VarBool name -> M.findWithDefault e name map_
    BinOp op e1 e2 -> BinOp op (subst1 map_ e1) (subst1 map_ e2)
    UnOp op e1     -> UnOp  op (subst1 map_ e1)
    Forall var e   -> Forall var (subst1 map_ e)
    Lit b          -> e

subst2 :: Map Name (Expr Integer) -> Expr a -> Expr a
subst2 map_ e =
  case e of
    VarInt name -> M.findWithDefault e name map_
    BinOp op e1 e2 -> BinOp op (subst2 map_ e1) (subst2 map_ e2)
    UnOp op e1     -> UnOp  op (subst2 map_ e1)
    Forall var e   -> Forall var (subst2 map_ e)
    Lit b          -> e

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-- | Swap two variables using tmp
var x:int, y:int, a:int, b:int in
  assume (x = a /\ y = b);
  var tmp:int in
    tmp := x;
    x := y;
    y := tmp:
  end;
  assert (x = b /\ y = a);
end
-}
swap1 :: Stmt
swap1 = vars ["x" ::: int, "y" ::: int, "b" ::: int,  "a" ::: int]
          [assume ((vi "x" =:= vi "a") /\: (vi "y" =:= vi "b"))
          ,vars ["tmp" ::: int]
            [ asgi ["tmp"] [vi "x"]
            , asgi ["x"]   [vi "y"]
            , asgi ["y"]   [vi "tmp"]]
          ,assert ((vi "x" =:= vi "b") /\: (vi "y" =:= vi "a"))]

{-- | Swap two variables (no aux var)
var x:int, y:int, a:int, b:int in
  assume (x = a /\ y = b);
  x := x + y;
  y := x - y;
  x := x - y:
  end;
  assert (x = b /\ y = a);
end
-}
swap2 :: Stmt
swap2 = vars ["x" ::: int, "y" ::: int, "b" ::: int,  "a" ::: int]
          [ assume ((vi "x" =:= vi "a") /\: (vi "y" =:= vi "b"))
          , asgi ["x"]   [vi "x" +: vi "y"]
          , asgi ["y"]   [vi "x" -: vi "y"]
          , asgi ["x"]   [vi "x" -: vi "y"]
          , assert ((vi "x" =:= vi "b") /\: (vi "y" =:= vi "a"))]

{-- | Swap two array elements
var a:[int], j:int, i:int, x:int, y:int in
  assume (a[i] = x /\ a[j] = y) ;
  var tmp in
    tmp  := a[i];
    a[i] := a[j];
    a[j] := tmp:
  end
  assert (a[i] = y /\ a[j] = x);
end
-}
swaparr :: Stmt
swaparr = vars ["a" ::: intarr, "i" ::: int, "y" ::: int, "x" ::: int, "y" ::: int]
      [ assume (((ai "a" |: vi "i") =:= vi "x") /\: ((ai "a" |: vi "j") =:= vi "y"))
      , vars ["tmp" ::: int]
          [ asgi  ["tmp"] [ai "a" |: vi "i"]]
          -- , asgai [""]    [vi "x" -: vi "y"]
          -- , asgai ["x"]   [vi "x" -: vi "y"]]
      , assume (((ai "a" |: vi "i") =:= vi "y") /\: ((ai "a" |: vi "j") =:= vi "x"))]

{-- | Example D1
var x:int, y:iny in
  assume 0<x ;
  inv 0<=x while 0<x { x := x-1 } ;
  y := x ;
  assert y=0;
end
-}
d1 :: Stmt
d1 = vars ["x" ::: int, "y" ::: int]
      [ assume (l 0 <: vi "x")
      , while  (l 0 <=: vi "x")
               (l 0 <: vi"x")
               (asgi ["x"] [vi "x" -: l 1])
      , asgi ["y"] [vi "x"]
      , assert (vi "y" =:= l 0)]

{-- | Example D2
var x:int, y:iny in
  assume 2<=x ;
  inv 0<=x while 0<x { x := x-2 } ;
  y := x ;
  assert y=0 ;
end
-}
d2 :: Stmt
d2 = vars ["x" ::: int, "y" ::: int]
      [ assume (l 2 <=: vi "x")
      , while  (l 0 <=: vi "x")
               (l 0 <: vi"x")
               (asgi ["x"] [vi "x" -: l 2])
      , asgi ["y"] [vi "x"]
      , assert (vi "y" =:= l 0)]

{-- | minind
var a:[int], i:int, N:int, i0:int in
  assume (i < N, i = i0)
  var min in
    r := a[i];
    min := i;
    inv (i <= N /\ forall j : i0 <= j < i : a[r] <= a[j]) while i<N do
      {assume (a[i] < min); min := a[i]; r := i;} [] {assume (not (a[i] < min));skip };
      i := i + 1;
      }
  end
  assert (forall j : i0 <= j < i: a[r] <= a[j])
end
-}
-- minind :: Stmt
-- minind = Scope ["a" ::: Array Int, "i" ::: Prim Int, "N" ::: Prim Int, "i0" ::: Prim Int, "r" ::: Prim Int]
--       (stmts [ Assume (BinOp (.<)  (VarInt "i")  (VarInt "N"))
--              , Assume (BinOp (.==) (VarInt "i")  (VarInt "i0"))
--              , Scope ["min" :::  Prim Int]
--                 (stmts
--                   [ AsgI ["r", "min"] [Arr "a" [VarInt "i"], VarInt "i"]
--                     While  (BinOp (.<=) (VarInt "i")  (VarInt "N"))
--                            (BinOp (.<)  (VarInt "i")  (VarInt "N"))
--                            (stmts [Choice (Assume (AsgI ["x"] [BinOp (-) (VarInt "x") (Lit 2)]])
--       , AsgI ["y"] [VarInt "x"]
--       , Assert (BinOp (.==) (VarInt "y") (Lit 0))])
