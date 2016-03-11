module Stmt where

import           Control.Monad.Writer         hiding ((<>))
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

import Var
import Expr

-- | Statement type
data Stmt
  = Skip
  | Assert (Expr Bool)
  | Assume (Expr Bool)
  | AsgI  [Name] [Expr Integer]
  | AsgAI [(Name,Expr Integer)] [Expr Integer]
  | AsgPC [Expr Integer] Name [Expr Integer]
  | Seq Stmt Stmt
  | Choice Stmt Stmt
  | While (Expr Bool) (Expr Bool) Stmt
  | WhileK Integer (Expr Bool) Stmt
  | Scope [Var] Stmt


-- Smart constructors
skip   = Skip
assert = Assert
assume = Assume
asgi  = AsgI
asgai = AsgAI
while = While
whileK = WhileK
stmts :: [Stmt] -> Stmt
stmts  = foldr Seq Skip
vars vs = Scope vs . foldr Seq Skip
choice :: [Stmt] -> Stmt
choice = foldr1 Choice

-- | WLP
wlp :: Stmt
    -> Expr Bool
    -> (Expr Bool, [Expr Bool])
wlp stmt q = runWriter (wlp' stmt q)

-- | Weakest liberal precondition: wlp S q
--   Writer monad keeps track of p.o. for while loops.
wlp' :: Stmt
     -> Expr Bool
     -> Writer [Expr Bool] (Expr Bool)
wlp' stmt q =
  case stmt of
    Skip     -> return q
    Assert p -> return (p /\  q)
    Assume p -> return (p ==> q)
    AsgI vars exprs    -> return (subst2 (M.fromList $ zip vars exprs) q)
    AsgAI [(n,ix)] [expr] -> return (cond1 (splice (n,ix) expr q))
    Seq s1 s2       -> wlp' s2 q >>= wlp' s1
    Choice s1 s2    -> liftM2 (/\) (wlp' s1 q) (wlp' s2 q)
    While inv cond s ->
      do wloop <- wlp' s inv
         tell [ boundVars $ inv /\ neg cond  ==> q
              , boundVars $ inv /\ cond      ==> wloop]
         return inv
    WhileK 0 cond s -> return (neg cond /\ q)
    WhileK n cond s -> do
      wk <- wlp' (WhileK (n-1) cond s) q >>= wlp' s
      return $ (cond /\ wk) \/ (neg cond /\ q)
    Scope vs s ->
      do w <- wlp' s q
         return (foralls vs w)

-- fixpoint :: (Stmt -> Expr Bool -> Expr Bool) -> Expr Bool -> Stmt -> Expr Bool -> Expr Bool
-- fixpoint wlp g s q =
--   let  
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance Pretty Stmt where
  pretty stmt =
    case stmt of
      Skip     -> text "skip"
      Assert e -> hcat [green $ text "assert", pretty e]
      Assume e -> hcat [magenta $ text "assume", pretty e]
      AsgI n e -> hsep [ hcat $ punctuate (comma <> space) (map text n)
                       , text ":="
                       , hcat $ punctuate (comma <> space) (map pretty e)]
      AsgAI ni e -> hsep [ hcat $ punctuate (comma <> space) (map (\(n,ix) -> text n <> brackets (pretty ix)) ni)
                        , text ":="
                        , hcat $ punctuate (comma <> space) (map pretty e)]
      Seq  s1 s2   -> vcat $ punctuate (semi <> space) [pretty s1, pretty s2]
      Choice s1 s2 -> hcat [pretty s1, text "[]", pretty s2]
      While  i c s -> vcat [ hsep [yellow $ text "inv", pretty i, yellow $ text "while", pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      WhileK i c s -> vcat [ hsep [(yellow $ text "while") <> brackets (red $ pretty i) , pretty c, yellow $ text "do"]
                           , indent 2 (braces $ pretty s)]
      Scope vs s   -> vcat [hsep [text "vars", hsep $ punctuate comma (map pretty vs), text "in"]
                           , indent 2 (pretty s)
                           ,text "end"]
