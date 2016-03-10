module Var where

import           Text.PrettyPrint.ANSI.Leijen hiding (bool, int)

-- | Type of identifier (for now string)
type Name = String

-- | Variable type
data Var = Name ::: Type

data Type = Prim PrimitiveType | Array PrimitiveType

instance Eq Var where
  (n1 ::: _) == (n2 ::: _) = n1 == n2

instance Pretty Var where
  pretty (name ::: type') = hcat [text name, text ":", pretty type']

int :: Type
int = Prim Int

bool :: Type
bool = Prim Bool

intarr = Array Int
boolarr = Array Bool

instance Pretty Type where
  pretty (Prim t)  = pretty t
  pretty (Array t) = brackets (pretty t)

data PrimitiveType = Int | Bool

instance Pretty PrimitiveType where
  pretty Int  = text "int"
  pretty Bool = text "bool"

