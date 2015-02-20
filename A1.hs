{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
--module A1 where

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate)
import Debug.Trace (trace)

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
    deriving (Eq, Ord, Data, Typeable, Show)

type Parameters = [Variable]

data Variable = Variable [Credential] Name Type
              deriving (Eq, Ord, Data, Typeable, Show)

type BoundVariable =(Name, Type)
                   

data Credential = Credential --TODO optional?
                  deriving (Eq, Ord, Data, Typeable, Show)

data AssignTarget =
  VarTarget Name
  | ArrTarget ArrName Expression
  deriving (Eq, Ord, Data, Typeable, Show)

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
    | RepBy Expression Expression Expression --internal use only 
      deriving (Eq, Ord, Data, Typeable, Show)

newtype Name = ToName {fromName :: String}
               deriving (Eq, Ord, Data, Typeable)

instance Show Name where
  show = fromName
                        
type ArrName = Name --TODO is this okay?
         
--newtype ArrName = ToArrName String
               -- | RepBy ArrName Expression Expression
--                  deriving (Eq, Ord, Data, Typeable)

--instance Show ArrName where
--  show (ToArrName s) = s
  --show (RepBy arr ind exp) = parens $ "store" +-+ (parens $ show arr) +-+ (toZ3 ind) +-+ (toZ3 exp) 
                          
newtype ProgramName = ToProgName {fromProgName :: String}
                      deriving (Eq, Ord, Data, Typeable)

data BinaryOp = Plus | Minus | Times | Div | Or | And | LOr | LAnd | Implies | Lt | Leq | Gt | Geq | Eq
    deriving (Eq, Ord, Data, Typeable)

data Type = Type PrimitiveType | ArrayType PrimitiveType
                                 deriving (Eq, Ord, Data, Typeable)

data PrimitiveType = IntT | BoolT
                            deriving (Eq, Ord, Data, Typeable)

--data ArrayType = ArrayType PrimitiveType
--                 deriving (Eq, Ord, Data, Typeable)

type Variables = [Variable]
type Expressions = [Expression]
type AssignTargets = [AssignTarget]


--We treat expressions as predicates, since our language
--Can explain all necessary predicates
type Pred = Expression

--toPred :: Expression -> Pred
--toPred = error "TODO implement toPred"

----------------------------------------------------------


getVarTargets :: [AssignTarget] -> [Name]
getVarTargets targets = 
  concatMap (\t -> case t of
                VarTarget n -> [n]
                _ -> []) targets

getArrTargets :: [AssignTarget] -> [(Name, Expression)]
getArrTargets targets = 
  concatMap (\t -> case t of
                ArrTarget n i -> [(n, i)]
                _ -> []) targets
                
wlp :: Statement -> Pred -> Pred
wlp Skip q = q
wlp (Assert p) q = BinOp p LAnd q
wlp (Assume p) q = BinOp p Implies q
wlp (Assign targets exp) q =
  let
    sub1 = subExpForName (getVarTargets targets) exp q
    sub2 = subExpForArrName (getArrTargets targets) exp sub1
  in sub2 --TODO make simultaneous?
wlp (Return s) q = error "TODO implement return"
wlp (NonDet s1 s2) q = BinOp (wlp s1 q) LAnd (wlp s2 q)
wlp (Seq s1 s2) q = wlp s1 (wlp s2 q)
--We trust programmer's annotation
wlp (Loop invar _guard _body) q = invar
wlp (Var vars s) q = wlp s q --TODO is this right? 

subOneLevel :: [Name] ->  Expression -> Expression -> Expression
subOneLevel names subExp e@(EName varName)   =
  if (varName `elem` names)
  then subExp
  else e
--subOneLevel names subExp e@(ArrAccess arrName expr) =
--  if (Set.member (ArrTarget arrName expr) names) then subExp else e
subOneLevel _ _ e = e --TODO is array case right?

subExpForName :: (Data a) => [Name] -> Expression -> a -> a
subExpForName names subExp = everywhere (mkT $ subOneLevel names subExp)

subOneLevelArr :: [(Name, Expression)] -> Expression -> Expression -> Expression
subOneLevelArr nameIndexPairs subExpr e@(EName varName) =
  let
    nameIndList = filter (\(n,_) -> n == varName) nameIndexPairs
  in case nameIndList of
    [] -> e
    [(_,i)] -> RepBy (EName varName) i subExpr
    --TODO multi case?
subOneLevelArr l subExp e = e

subExpForArrName :: (Data a) => [(Name, Expression)] -> Expression -> a -> a
subExpForArrName names subExp = everywhere (mkT $ subOneLevelArr names subExp)

--Special version for arrays

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

toZ3 :: Pred -> String
toZ3 (IntLit l) = show l
toZ3 (BoolLit l) = if l then "true" else "false"
toZ3 (EName n) = show n
toZ3 (BinOp e1 op e2) = parens $ (show op) +-+ (toZ3 e1) +-+ (toZ3 e2) 
toZ3 (LNot p) = parens $ "not" +-+ toZ3 p
toZ3 FunctionCall = error "Can't convert function call to Z3" --TODO
toZ3 (Forall (v,t) p) = parens $ "forall" +-+ (parens $ parens $ show v +-+ show t) +-+ toZ3 p 
toZ3 (ArrAccess arr i) = parens $ "select" +-+ (show arr) +-+ (toZ3 i) 
toZ3 (IfThenElse p1 p2 p3) = parens "ite" +-+ (toZ3 p1) +-+ (toZ3 p2) +-+ (toZ3 p3)

parens s = "(" ++ s ++ ")"

formatZ3 :: Pred -> String
formatZ3 p = intercalate "\n" [
  parens $ "assert" +-+ toZ3 (LNot p),
  parens $ "check-sat"
  ]

--Generate the Z3 code checking if the given statement matches the given post-condition
z3wlp :: Statement -> Expression -> String
z3wlp s q =
  let
    varDec (Variable _ v t) = parens $ "declare-const" +-+ show v +-+ show t
    varDecs vars = foldr (\v decs -> decs ++ "\n" ++ varDec v) "" vars
  in (varDecs (freeVars s) ++ "\n") ++ (formatZ3 $ wlp s q) 



prog1 = Assert (BinOp (IntLit 3) Leq (IntLit 3))

isSorted :: Statement
isSorted =
  Var [
    Variable [] (ToName "arr")  (ArrayType IntT),
    Variable [] (ToName "i") (Type IntT),
    Variable [] (ToName "isSorted") (Type BoolT),
    Variable [] (ToName "n") (Type IntT)
    ] $
  "isSorted" `assign` (BoolLit False) `Seq`
  while
  ((var "isSorted" `implies`
    Forall (ToName "j",Type IntT ) ((var "j" `lt` var "i") `implies`
                                    (ArrAccess (ToName "arr") (var "j") `leq` ArrAccess (ToName "arr") (var "j" `plus` IntLit 1)
                                      ))))
  ( (var "i") `leq` (var "n")) (
    (ifelse ((ArrAccess (ToName "arr") (var "i")) `leq` (ArrAccess (ToName "arr") (var "i" `plus` IntLit 1)))
      ("isSorted" `assign` (BoolLit False))
      (Skip) ) `Seq`
    ("i" `assign` (var "i" `plus` IntLit 1))
    ) `Seq`
  Skip


simpleAssignTest :: (Statement, Expression)
simpleAssignTest = (s,q)
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        "x" `assign` (IntLit 3 `plus` IntLit 4)
    q = ((var "x") `eq` IntLit 7)


--Helper functions

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
and = binop And
or = binop Or

land = binop LAnd
lor = binop LOr
implies = binop Implies



plus = binop Plus
minus = binop Minus
times = binop Times
div = binop Div



ifelse :: Expression -> Statement -> Statement -> Statement
ifelse g s1 s2 = (Assume g `Seq` s1) `NonDet` (Assume (LNot g) `Seq` s2) 

assign :: String -> Expression -> Statement
s `assign` e = Assign [VarTarget $ ToName s] (e)

{-
main :: IO ()
main = do
  let z3 = z3wlp (fst simpleAssignTest) (snd simpleAssignTest) 
      
      
  writeFile "/home/joey/stuff/PV/test.z3" z3
  --putStrLn z3
-}


main :: IO ()
main = do
  let z3 = z3wlp isSorted $ Forall (ToName "j", Type IntT) $
                            ArrAccess (ToName "arr") (var "j") `leq`
                            ArrAccess (ToName "arr") (var "j" `plus` IntLit 1) 
      
      
  writeFile "/home/joey/stuff/PV/test.z3" z3
  --putStrLn z3

