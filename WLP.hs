{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
module WLP where

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate)
import Debug.Trace (trace)

import Control.Monad (forM)

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
                  deriving (Eq, Ord, Data, Typeable, Show)

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
    | RepBy Expression Expression Expression --internal use only 
      deriving (Eq, Ord, Data, Typeable)

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

--Given a statement and an expression, return its wlp and a list of indvariant conditions to check  
wlp :: Statement -> Expression -> (Expression, [Expression])
wlp Skip q = (q, [])
wlp (Assert p) q = (BinOp p LAnd q, [])
wlp (Assume p) q = (BinOp p Implies q, [])
wlp (Assign targets exp) q =
  let
    sub1 = subExpForName (getVarTargets targets) exp q
    sub2 = subExpForArrName (getArrTargets targets) exp sub1
  in (sub2, []) --TODO make simultaneous?
wlp (Return s) q = error "TODO implement return"
wlp (NonDet s1 s2) q =
  let
    (sub1, checks1) = (wlp s1 q)
    (sub2, checks2) = (wlp s2 q) 
  in (BinOp sub1 LAnd sub2, checks1 ++ checks2)
wlp (Seq s1 s2) q =
  let
    (sub1, checks1) = (wlp s2 q)
    (sub2, checks2) = wlp s1 sub1
  in (sub2, checks1 ++ checks2)
--In this case, we must check that our invariant holds, so we generate our checks
wlp (Loop invar guard body) q = let
    (subWLP, subConds) = wlp body invar
  in (invar, [
      BinOp (BinOp invar LAnd (LNot guard)) Implies q
      ,BinOp (BinOp invar LAnd guard) Implies subWLP ]
     ++ subConds)
wlp (Var vars s) q = wlp s q --TODO credentials 

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







