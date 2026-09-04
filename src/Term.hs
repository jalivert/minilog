module Term where

import Data.List ( intercalate )


-- | The syntactic forms of Minilog. In short: a `Term` is anything that
-- can sit inside a struct, a `Goal` is anything we can try to prove, and
-- a `Predicate` is one entry of the knowledge base (a fact or a rule).
-- The `Show` instances print everything back in Prolog syntax.


data Goal = Call !Struct
          | Unify !Term !Term
  deriving (Eq)


data Predicate  = Fact !Struct
                | !Struct :- ![Goal]
  deriving (Eq)


data Struct = Struct{ name :: !String, args :: ![Term] }
  deriving (Eq)


data Term = Var !String
          | Atom !String
          | Compound !Struct
          | Wildcard
  deriving (Eq)


instance Show Goal where
  show (Call struct) = show struct
  show (Unify val'l val'r) = show val'l ++ " = " ++ show val'r


instance Show Predicate where
  show (Fact struct) = show struct ++ "."
  show (head :- body) = show head ++ " :- " ++ intercalate " , " (map show body) ++ "."


instance Show Struct where
  show Struct{ name, args = [] } = name
  show Struct{ name, args } = name ++ "(" ++ intercalate ", " (map show args) ++ ")"


instance Show Term where
  show (Var name) = name
  show (Atom name) = name
  show (Compound struct) = show struct
  show Wildcard = "_"
