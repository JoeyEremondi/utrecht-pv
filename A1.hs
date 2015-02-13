{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
--module A1 where

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate)

--We declare our recursive data types initially as open types
-- (i.e. a variable for the recursive part)
--

data Program = Program ProgramName Parameters Statement

data Statement =
  Skip
  | Assert Expression
  | Assume Expression
  | Assign AssignTargets Expression
  | Return Expression
  | Seq Statement Statement
  | NonDet Statement Statement
  | Loop Expression Expression Statement
  | Var Variables Statement
    deriving (Eq, Ord, Data, Typeable)

type Parameters = [Variable]
data Variable = Variable [Credential] Name Type
              deriving (Eq, Ord, Data, Typeable)

type BoundVariable =(Name, Type)
                   

data Credential = Credential --TODO optional?
                  deriving (Eq, Ord, Data, Typeable)

data AssignTarget =
  VarTarget Name
  | ArrTarget ArrName Expression
  deriving (Eq, Ord, Data, Typeable)

data Expression =
    IntLit Int
    | BoolLit Bool
    | EName Name
    | BinOp Expression BinaryOp Expression
    | LNot Expression
    | FunctionCall -- TODO this case
    | Forall BoundVariable Expression
    | ArrAccess ArrName Expression
    | IfThenElse Expression Expression Expression
      deriving (Eq, Ord, Data, Typeable)

newtype Name = ToName {fromName :: String}
               deriving (Eq, Ord, Data, Typeable, Show)
                        
                        
newtype ArrName = ToArrName {fromArrName :: String}
                  deriving (Eq, Ord, Data, Typeable)
                           
newtype ProgramName = ToProgName {fromProgName :: String}
                      deriving (Eq, Ord, Data, Typeable)

data BinaryOp = Plus | Minus | Times | Div | Or | And | LOr | LAnd | Implies | Lt | Leq | Gt | Geq | Eq
    deriving (Eq, Ord, Data, Typeable)

data Type = Type PrimitiveType | ArrType ArrayType
                                 deriving (Eq, Ord, Data, Typeable)

data PrimitiveType = IntT | BoolT
                            deriving (Eq, Ord, Data, Typeable)

data ArrayType = ArrayType PrimitiveType
                 deriving (Eq, Ord, Data, Typeable)

type Variables = [Variable]
type Expressions = [Expression]
type AssignTargets = [AssignTarget]

----------- Predicates we can reason about ---------------
{-
data Pred =
  PVar Name
  | PAnd Pred Pred
  | POr Pred Pred
  | PNot Pred
  | PForall Name Pred
  | PExists Name Pred
  | PImplies Pred Pred
    deriving (Data, Typeable)
-}

--We treat expressions as predicates, since our language
--Can explain all necessary predicates
type Pred = Expression

toPred :: Expression -> Pred
toPred = error "TODO implement"

wlp :: Statement -> Pred -> Pred
wlp Skip q = q
wlp (Assert p) q = BinOp p LAnd q
wlp (Assume p) q = BinOp p Implies q
wlp (Assign targets exp) q = subExpForName (Set.fromList targets) exp q
wlp (Return s) q = error "TODO implement"
wlp (NonDet s1 s2) q = BinOp (wlp s1 q) LAnd (wlp s2 q)
wlp (Seq s1 s2) q = wlp s1 (wlp s2 q)
--We trust programmer's annotation
wlp (Loop invar _guard _body) q = toPred invar
wlp (Var s1 s2) q = error "TODO implement"

subOneLevel :: Set.Set AssignTarget ->  Expression -> Expression -> Expression
subOneLevel names subExp e@(EName varName)   =
  if (Set.member (VarTarget varName) names) then subExp else e
subOneLevel names subExp e@(ArrAccess arrName expr) =
  if (Set.member (ArrTarget arrName expr) names) then subExp else e
subOneLevel _ _ e = e

subExpForName :: Data a => Set.Set AssignTarget -> Expression -> a -> a
subExpForName names subExp = everywhere (mkT $ subOneLevel names subExp)

---------------------Z3 generation---------------------------------
instance Show Type  where
  show = showType

showType :: Type -> String
showType (Type IntT) = "Int"
showType (Type BoolT) = "Bool"
showType (ArrType (ArrayType IntT)) = parens $ "Array Int Int" 
showType (ArrType (ArrayType BoolT)) = parens $ "Array Int Bool"   

freeVarDecl :: (Name, Type) -> String
freeVarDecl (n,t) = parens $ "declare-const " ++ show n ++ " " ++ (show t)

x +-+ y = x ++ " " ++ y

showBinOp :: BinaryOp -> String
showBinOp Plus = "+"
showBinOp Minus = "-"
showBinOp Times = "*"
showBinOp Div = "/"
showBinOp Or = "or"
showBinOp And = "and"
showBinOp LOr = "or"
showBinOp LAnd = "and" --TODO same?
showBinOp Implies = "=>"
showBinOp Lt = "<"
showBinOp Leq = "<="
showBinOp Gt = ">"
showBinOp Geq = ">="
showBinOp Eq = "="

instance Show BinaryOp where
  show = showBinOp

toZ3 :: Pred -> String
toZ3 (IntLit l) = show l
toZ3 (BoolLit l) = if l then "true" else "false"
toZ3 (EName n) = show n
toZ3 (BinOp e1 op e2) = parens $ (show op) +-+ (toZ3 e1) +-+ (toZ3 e2) 
toZ3 (LNot p) = parens $ "not" +-+ toZ3 p
toZ3 FunctionCall = error "Can't convert function call to Z3" --TODO
toZ3 (Forall v p) = parens $ "forall" +-+ (parens $ show v) +-+ toZ3 p 
toZ3 (ArrAccess p1 p2) = error "Can't represent arrays in Z3" --TODO
toZ3 (IfThenElse p1 p2 p3) = parens "ite" +-+ (toZ3 p1) +-+ (toZ3 p2) +-+ (toZ3 p3)

parens s = "(" ++ s ++ ")"

formatZ3 :: Pred -> String
formatZ3 p = intercalate "\n" [
  parens $ "assert" +-+ toZ3 (LNot p),
  parens $ "check-sat"
  ]

--Generate the Z3 code checking if the given statement matches the given post-condition
z3wlp :: Statement -> Expression -> String
z3wlp s q = formatZ3 $ wlp s q 

main :: IO ()
main = do
  let z3 = z3wlp prog1 (BoolLit True)
  writeFile "/home/joey/stuff/PV/test.z3" z3
  --putStrLn z3

prog1 = Assert (BinOp (IntLit 3) Leq (IntLit 3))
