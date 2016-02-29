{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
module Solver where

import Data.Map (Map)
import qualified Data.Map as M
import Data.SBV

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

data Expr t where
  Lit    :: n -> Expr n
  VarInt :: Name -> Expr Integer

  VarBool   :: Name -> Expr Bool

  Forall    :: Var -> Expr Bool -> Expr Bool

  UnOp      :: (SymWord a, SymWord b, Show a, Show b) => (SBV a -> SBV b) -> Expr a -> Expr b
  BinOp     :: (SymWord a, SymWord b, Show a, Show b) => (SBV a -> SBV a -> SBV b) -> Expr a -> Expr a -> Expr b
--  Arr       :: Name -> Expr Integer -> Expr a

instance Show t => Show (Expr t) where
  show (Lit n)    = show n
  show (VarInt n)  = n
  show (VarBool n) = n
  show (Forall var expr)  = "forall " ++ show var ++ ". " ++ show expr
  show (BinOp  op  e1 e2) = show e1 ++ " op " ++ show e2
  show (UnOp   op  e1)    = "op " ++ show e1

data IntOp  = Plus | Minus
data BoolOp = And | Or | Imply

data Var = Name ::: Type deriving (Show)

data Type = Prim PrimitiveType | Array PrimitiveType

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
         symVar <- forall var
         interpret envI (M.insert var symVar envB) expr
        Prim Int -> do
         symVar <- forall var
         interpret (M.insert var symVar envI) envB expr
    BinOp op e1 e2 -> do
       sym1 <- interpret envI envB e1
       sym2 <- interpret envI envB e2
       return (op sym1 sym2)
    UnOp op e1 -> do
       sym1 <- interpret envI envB e1
       return (op sym1)

example = Forall ("x" ::: Prim Int) (BinOp (.==) (VarInt "x") (Lit 1))

stmts :: [Stmt] -> Stmt
stmts = foldr Seq Skip



wlp :: Stmt
    -> Expr Bool
    -> Expr Bool
wlp stmt q =
  case stmt of
    Skip -> q
    Assert p -> BinOp (&&&) p q
    Assume p -> BinOp (==>) p q
    AsgB vars exprs -> subst1 (M.fromList $ zip vars exprs) q
    AsgI vars exprs -> subst2 (M.fromList $ zip vars exprs) q
    Seq s1 s2 -> wlp s1 (wlp s2 q)
    Choice s1 s2 -> BinOp (&&&) (wlp s1 q) (wlp s2 q)
    While inv cond s -> BinOp (&&&) (BinOp (==>) (BinOp (&&&) (UnOp bnot cond) inv) q)
                                    (BinOp (==>) (BinOp (&&&) cond inv) (wlp s cond))
    Scope vs s -> foldr  Forall (wlp s q) vs

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
swap = Scope ["x" ::: Prim Int, "y" ::: Prim Int, "b" ::: Prim Int,  "a" ::: Prim Int]
        (stmts [ Assume (BinOp (&&&) (BinOp (.==) (VarInt "x") (VarInt "a"))
                                     (BinOp (.==) (VarInt "y") (VarInt "b")))
               , Scope ["tmp" ::: Prim Int]
                  (stmts [AsgI ["tmp"] [VarInt "x"]
                         , AsgI ["x"]   [VarInt "y"]
                         , AsgI ["y"]   [VarInt "tmp"]])
               , Assert (BinOp (&&&) (BinOp (.==) (VarInt "x") (VarInt "b"))
                                     (BinOp (.==) (VarInt "y") (VarInt "a"))) ])

{-- | Example D1
var x:int, y:iny in
  assume 0<x ;
  inv 0<=x while 0<x { x := x-1 } ;
  y := x ;
  assert y=0;
end
-}
d1 :: Stmt
d1 = Scope ["x" ::: Prim Int, "y" ::: Prim Int]
      (stmts [ Assume (BinOp (.<)  (Lit 0)  (VarInt "x"))
             , While  (BinOp (.<=) (Lit 0)  (VarInt "x"))
                      (BinOp (.<)  (Lit 0)  (VarInt "x"))
                      (stmts [AsgI ["x"] [BinOp (-) (VarInt "x") (Lit 1)]])
      , AsgI ["y"] [VarInt "x"]
      , Assert (BinOp (.==) (VarInt "y") (Lit 0))])

{-- | Example D2
var x:int, y:iny in
  assume 2<=x ;
  inv 0<=x while 0<x { x := x-2 } ;
  y := x ;
  assert y=0 ;
end
-}
d2 :: Stmt
d2 = Scope ["x" ::: Prim Int, "y" ::: Prim Int]
      (stmts [ Assume (BinOp (.<=)  (Lit 2)  (VarInt "x"))
             , While  (BinOp (.<=) (Lit 0)  (VarInt "x"))
                      (BinOp (.<)  (Lit 0)  (VarInt "x"))
                      (stmts [AsgI ["x"] [BinOp (-) (VarInt "x") (Lit 2)]])
      , AsgI ["y"] [VarInt "x"]
      , Assert (BinOp (.==) (VarInt "y") (Lit 0))])
