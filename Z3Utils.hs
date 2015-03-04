{-# LANGUAGE StandaloneDeriving #-}
{-
Joseph Eremondi
Program Verification
UU# 4229924
March 4, 2015
-}

--Helper functions for converting GCL to Z3 code
--And for calling Z3 from the command line
module Z3Utils where

import Types
--import WLP
import Data.List (intercalate)
import qualified Data.Map as Map

import System.Process (readProcessWithExitCode)
import System.Exit

import System.IO.Unsafe (unsafePerformIO)

deriving instance Show ProgramName
deriving instance Show Statement
deriving instance Show Variable
deriving instance Show AssignTarget
deriving instance Show Expression
deriving instance Show Program

--Below are a bunch of helper functions, which make writing programs in our GCL variant much nicer

while :: Expression -> Expression -> Statement -> Statement
while inv g s = Loop (Just inv) g s

while_ :: Expression -> Statement -> Statement
while_ g s = Loop Nothing g s

var str = EName (ToName str)

callFn varStr str es = FnCallAssign (VarTarget $ ToName varStr) (ToProgName str) es

callUnqual fnName es = UninterpCall (fnName) es

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
divv = binop Div

ifelse :: Expression -> Statement -> Statement -> Statement
ifelse g s1 s2 = ( (Assume g) `Seq` s1) `NonDet` ( (Assume (LNot g) ) `Seq` s2) 

assign :: String -> Expression -> Statement
s `assign` e = Assign [VarTarget $ ToName s] (e)

------------------------------------------------------

--Z3 formatting functions

--Simple helper for wrapping string in parentheses
parens s = "(" ++ s ++ ")"

--Concatenate with a space, used often
x +-+ y = x ++ " " ++ y

{-
Convert an expression (predicate) into Z3 syntax
-}
toZ3 :: Expression -> String
toZ3 (IntLit l) =  show l
toZ3 (BoolLit l) =  if l then "true" else "false"
toZ3 (EName n) = show n
toZ3 (BinOp e1 op e2) = parens $ (show op) +-+ (toZ3 e1) +-+ (toZ3 e2) 
toZ3 (LNot p) = parens $ "not" +-+ toZ3 p
toZ3 (UninterpCall name params) = parens $ name +-+ ( intercalate " " (map toZ3 params))
toZ3 (Forall (v,t) p) = parens $ "forall" +-+ (parens $ parens $ show v +-+ show t) +-+ toZ3 p 
toZ3 (ArrAccess arr i) = parens $ "select" +-+ (show arr) +-+ (toZ3 i) 
toZ3 (IfThenElse p1 p2 p3) = parens $  "ite" +-+ (toZ3 p1) +-+ (toZ3 p2) +-+ (toZ3 p3)
toZ3 (RepBy e1 e2 e3) = parens $ "store" +-+ (toZ3 e1) +-+ (toZ3 e2) +-+ (toZ3 e3)

{-
To verify an expression is valid, we negate it,
then check if the negation is satisfiable
-}
formatZ3 :: Expression -> String
formatZ3 p = intercalate "\n" [
  parens $ "assert" +-+ toZ3 (LNot p),
  parens $ "check-sat"
  ]

instance Show Type  where
  show = showType

{-
Traverse a statement and get any variables declared,
so that we can declare them in Z3 with the proper types
-}
freeVars :: Statement -> Variables
freeVars Skip = []
freeVars (Assert s) = []
freeVars (Assume s) = []
freeVars (Assign s1 s2) = []
freeVars (Seq s1 s2) = freeVars s1 ++ freeVars s2
freeVars (NonDet s1 s2) = freeVars s1 ++ freeVars s2
freeVars (Loop _ _ s) = freeVars s
freeVars (Var vars s) = vars ++ freeVars s
freeVars (Return s) = [] 
freeVars (FnCallAssign _ _ _) = [] 

{-
Same as freeVars, but traverses the body of a function
-}
progFreeVars :: Program -> Variables
progFreeVars (Program _ params body ty) = [Variable [] (ToName "return") ty]
                                       ++ params ++ (freeVars body)
{-
Convert our types into the format Z3 can read
-}
showType :: Type -> String
showType (Type IntT) = "Int"
showType (Type BoolT) = "Bool"
showType (ArrayType IntT) = parens $ "Array Int Int" 
showType (ArrayType BoolT) = parens $ "Array Int Bool"   


--Binops in Z3 format
showBinOp :: BinaryOp -> String
showBinOp Plus = "+"
showBinOp Minus = "-"
showBinOp Times = "*"
showBinOp Div = "/"
showBinOp Or = "or"
showBinOp And = "and"
showBinOp LOr = "or"
showBinOp LAnd = "and"
showBinOp Implies = "=>"
showBinOp Lt = "<"
showBinOp Leq = "<="
showBinOp Gt = ">"
showBinOp Geq = ">="
showBinOp Eq = "="

instance Show BinaryOp where
  show = showBinOp

{-
Given a variable, generate the Z3 declaration to go at the top of thefile to be tested
-}
varDec :: Variable -> String
varDec (Variable _ v t) = parens $ "declare-const" +-+ show v +-+ show t

--Given a statement (where we get free variables) and an expression,
--Covnert the expression into Z3 format for validity testing
makeZ3String :: Statement -> Expression -> String
makeZ3String s p =
  let
    varDecs vars = foldr (\v decs -> decs ++ "\n" ++ varDec v) "" vars
   in (varDecs (freeVars s) ++ "\n") ++ (formatZ3 $ p )

{-
Given a string asserting the negation of an expression, with free vars declared,
invoke the command "z3" to check for validity.
Will fail if Z3 is not installed
-}
z3IsValid :: String -> IO Bool
z3IsValid checkFile = do
  (code, stdout, stderr) <- readProcessWithExitCode "z3" ["-in"] checkFile
  case (code, stdout, stderr) of
        (ExitSuccess, "unsat\n", "") -> return True
        (ExitSuccess, "sat\n", "") -> return False
        r -> error $ "Z3 error: " ++ (show r) ++ "\n" ++ checkFile

{-
Given a string asserting the negation of an expression, with free vars declared,
invoke the command "z3" to check for validity, and if a counter-example is found,
then return the found model as a string
-}  
getModel :: String -> IO String
getModel checkFile = do
  (_code, stdout, _stderr) <- readProcessWithExitCode "z3" ["-in"] (checkFile ++ "\n(get-model)")
  return stdout

{-
Use Z3 to test of two predicates are equivalent, with the free-variables
of the given statement declared.
Useful in fixpoint invariant generation.
-}
z3iff :: Statement -> Expression -> Expression -> Bool
z3iff s e1 e2 = unsafePerformIO $ z3IsValid $ makeZ3String s (e1 `iff` e2)
