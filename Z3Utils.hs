{-# LANGUAGE StandaloneDeriving #-}
module Z3Utils where

import WLP
import Data.List (intercalate)

deriving instance Show Statement
deriving instance Show Variable
deriving instance Show AssignTarget
deriving instance Show Expression

while :: Expression -> Expression -> Statement -> Statement
while inv g s = Loop inv g s

var str = EName (ToName str)

binop :: BinaryOp -> Expression -> Expression -> Expression
binop op e1 e2 = BinOp e1 op e2

eq = binop Eq
leq = binop Leq
geq = binop Geq
gt = binop Gt
lt = binop Lt
band = binop And
bor = binop Or

land = binop LAnd
lor = binop LOr
implies = binop Implies

x `iff` y = (x `implies` y) `land` (y `implies` x)


plus = binop Plus
minus = binop Minus
times = binop Times
div = binop Div

ifelse :: Expression -> Statement -> Statement -> Statement
ifelse g s1 s2 = ( (Assume g) `Seq` s1) `NonDet` ( (Assume (LNot g) ) `Seq` s2) 

assign :: String -> Expression -> Statement
s `assign` e = Assign [VarTarget $ ToName s] (e)









toZ3 :: Expression -> String
toZ3 (IntLit l) =  show l
toZ3 (BoolLit l) =  if l then "true" else "false"
toZ3 (EName n) = show n
toZ3 (BinOp e1 op e2) = parens $ (show op) +-+ (toZ3 e1) +-+ (toZ3 e2) 
toZ3 (LNot p) = parens $ "not" +-+ toZ3 p
toZ3 FunctionCall = error "Can't convert function call to Z3" --TODO
toZ3 (Forall (v,t) p) = parens $ "forall" +-+ (parens $ parens $ show v +-+ show t) +-+ toZ3 p 
toZ3 (ArrAccess arr i) = parens $ "select" +-+ (show arr) +-+ (toZ3 i) 
toZ3 (IfThenElse p1 p2 p3) = parens "ite" +-+ (toZ3 p1) +-+ (toZ3 p2) +-+ (toZ3 p3)

parens s = "(" ++ s ++ ")"

formatZ3 :: Expression -> String
formatZ3 p = intercalate "\n" [
  parens $ "assert" +-+ toZ3 (LNot p),
  parens $ "check-sat"
  ]

---------------------Z3 generation---------------------------------
instance Show Type  where
  show = showType

freeVars :: Statement -> Variables
freeVars Skip = []
freeVars (Assert s) = []
freeVars (Assume s) = []
freeVars (Assign s1 s2) = []
freeVars (Return s) = []
freeVars (Seq s1 s2) = freeVars s1 ++ freeVars s2
freeVars (NonDet s1 s2) = freeVars s1 ++ freeVars s2
freeVars (Loop _ _ s) = freeVars s
freeVars (Var vars s) = vars ++ freeVars s

showType :: Type -> String
showType (Type IntT) = "Int"
showType (Type BoolT) = "Bool"
showType (ArrayType IntT) = parens $ "Array Int Int" 
showType (ArrayType BoolT) = parens $ "Array Int Bool"   

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



--Generate the Z3 code checking if the given statement matches the given post-condition
z3wlp :: (Statement, Expression) -> (String, [String])
z3wlp (s, q) =
  let
    varDec (Variable _ v t) = parens $ "declare-const" +-+ show v +-+ show t
    varDecs vars = foldr (\v decs -> decs ++ "\n" ++ varDec v) "" vars
    (theWLP, conds)  = wlp s q
    formatPred p = (varDecs (freeVars s) ++ "\n") ++ (formatZ3 $ p )
  in  (formatPred theWLP, map formatPred conds)
