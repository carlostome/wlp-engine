{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
module Solver where

import Data.Map (Map)
import qualified Data.Map as M
import Data.SBV

-- | Statement type
data Stmt
  = Skip
  | Assert (Expr Bool)
  | Assume (Expr Bool)
  | AsgB [Name] [Expr Bool]
  | AsgI [Name] [Expr Integer]
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

data Expr t where
  Lit       :: n -> Expr n
  VarInt    :: Name -> Expr Integer

  VarBool   :: Name -> Expr Bool

  Forall    :: Var -> Expr Bool -> Expr Bool

  UnOp      :: Show a => UnOp a -> Expr a -> Expr a
  BinOp     :: (Show a, Show b, SymWord a, SymWord b) => BinOp a b -> Expr a -> Expr a -> Expr b
  Arr       :: Name -> Expr Integer -> Expr a

l = Lit
vi = VarInt
vb = VarBool
forall = Forall

(+:) :: Expr Integer -> Expr Integer -> Expr Integer 
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

not = UnOp (:!:)

data UnOp a where
  (:!:) :: UnOp Bool

deriving instance Show a => Show (UnOp a)

data BinOp a b where
  (:+:)  :: BinOp Integer Integer
  (:-:)  :: BinOp Integer Integer

  (:<:)  :: BinOp t Bool
  (:<=:) :: BinOp t Bool
  (:=:)  :: BinOp t Bool

  (:\/:) :: BinOp Bool Bool
  (:/\:) :: BinOp Bool Bool
  (:==>:)  :: BinOp Bool Bool

deriving instance (Show a, Show b) => Show (BinOp a b)

instance Show t => Show (Expr t) where
  show (Lit n)    = show n
  show (VarInt n)  = n
  show (VarBool n) = n
  show (Forall var expr)  = "forall " ++ show var ++ ". " ++ show expr
  show (BinOp  op  e1 e2) = show e1 ++ " " ++ show op ++ " " ++ show e2
  show (UnOp   op  e1)    = show op ++ " " ++ show e1

data Var = Name ::: Type deriving (Show)

data Type = Prim PrimitiveType | Array PrimitiveType
int :: Type
int = Prim Int

bool :: Type 
bool = Prim Bool

instance Show Type where
  show (Prim t)  = show t
  show (Array t) = "[" ++ show t ++ "]"

data PrimitiveType = Int | Bool deriving (Show)

type Name = String

-- data BinOp = Plus | Minus | And | Or | Impl | Lt | LEq | Eq

interpret :: SymWord t
          => Map Name SInteger
          -> Map Name SBool
          -> Expr t -> Symbolic (SBV t)
interpret envI envB expr =
  case expr of
    Lit n       -> return (literal n)
    VarInt name ->
      case M.lookup name envI of
        Nothing     -> error $ "Unbound variable: " ++ name
        Just val    -> return val
    VarBool name ->
      case M.lookup name envB of
        Nothing     -> error $ "Unbound variable: " ++ name
        Just val    -> return val
    Forall (var ::: type') expr ->
      case type' of
        Prim Bool -> do
         symVar <- Data.SBV.forall var
         interpret envI (M.insert var symVar envB) expr
        Prim Int -> do
         symVar <- Data.SBV.forall var
         interpret (M.insert var symVar envI) envB expr
    BinOp op e1 e2 -> do
       sym1 <- interpret envI envB e1
       sym2 <- interpret envI envB e2
       return ((getBinOp op) sym1 sym2)
    UnOp op e1 -> do
       sym1 <- interpret envI envB e1
       return ((getUnOp op) sym1)

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
    While inv cond s -> undefined
    Scope vs s -> foldr Forall (wlp s q) vs

check stmt = prove $ interpret M.empty M.empty (wlp stmt (Lit true))

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

{-- | Swap two variables
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
swap :: Stmt
swap = vars ["x" ::: int, "y" ::: int, "b" ::: int,  "a" ::: int]
            [ assume ((vi "x" =:= vi "a") /\: (vi "y" =:= vi "b"))
            , vars ["tmp" ::: int]
                   [ asgi ["tmp"] [vi "x"]
                   , asgi ["x"]   [vi "y"]
                   , asgi ["y"]   [vi "tmp"]]
            , assert ((vi "x" =:= vi "b") /\: (vi "y" =:= vi "a"))]

{-- | Example D1
var x:int, y:iny in
  assume 0<x ;
  inv 0<=x while 0<x { x := x-1 } ;
  y := x ;
  assert y=0;
end
-}
-- d1 :: Stmt
-- d1 = Scope ["x" ::: Prim Int, "y" ::: Prim Int]
--       (stmts [ Assume (BinOp (.<)  (Lit 0)  (VarInt "x"))
--              , While  (BinOp (.<=) (Lit 0)  (VarInt "x"))
--                       (BinOp (.<)  (Lit 0)  (VarInt "x"))
--                       (stmts [AsgI ["x"] [BinOp (-) (VarInt "x") (Lit 1)]])
--       , AsgI ["y"] [VarInt "x"]
--       , Assert (BinOp (.==) (VarInt "y") (Lit 0))])

{-- | Example D2
var x:int, y:iny in
  assume 2<=x ;
  inv 0<=x while 0<x { x := x-2 } ;
  y := x ;
  assert y=0 ;
end
-}
-- d2 :: Stmt
-- d2 = Scope ["x" ::: Prim Int, "y" ::: Prim Int]
--       (stmts [ Assume (BinOp (.<=)  (Lit 2)  (VarInt "x"))
--              , While  (BinOp (.<=) (Lit 0)  (VarInt "x"))
--                       (BinOp (.<)  (Lit 0)  (VarInt "x"))
--                       (stmts [AsgI ["x"] [BinOp (-) (VarInt "x") (Lit 2)]])
--       , AsgI ["y"] [VarInt "x"]
--       , Assert (BinOp (.==) (VarInt "y") (Lit 0))])

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
