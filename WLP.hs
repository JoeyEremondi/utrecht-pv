{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
module WLP where

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate)
import Debug.Trace (trace)

import Control.Monad (forM)
import qualified Data.Map as Map

--We declare our recursive data types initially as open types
-- (i.e. a variable for the recursive part)
--

data Program = Program ProgramName Parameters Statement

data Statement =
  Skip
  | Assert Expression
  | Assume Expression
  | Assign AssignTargets Expression
  | FnCallAssign AssignTarget ProgramName
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

type PostConds = Map.Map ProgramName Expression



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

--Given program postconditions,
-- a statement and an expression, return its wlp and a list of indvariant conditions to check
--We need the postconditions in order to allow function calls, since inferring
--Function postconditions is equivalent to inferring loop invariants, if we allow recursion 
wlp :: PostConds -> Statement -> Expression -> (Expression, [Expression])
wlp pconds Skip q = (q, [])
wlp pconds (Assert p) q = (BinOp p LAnd q, [])
wlp pconds (Assume p) q = (BinOp p Implies q, [])
wlp pconds (Assign targets exp) q =
  let
    sub1 = subExpForName (getVarTargets targets) exp q
    sub2 = subExpForArrName (getArrTargets targets) exp sub1
  in (sub2, []) --TODO make simultaneous?
wlp pconds (Return s) q = error "TODO implement return"
wlp pconds (NonDet s1 s2) q =
  let
    (sub1, checks1) = (wlp pconds s1 q)
    (sub2, checks2) = (wlp pconds s2 q) 
  in (BinOp sub1 LAnd sub2, checks1 ++ checks2)
wlp pconds (Seq s1 s2) q =
  let
    (sub1, checks1) = (wlp pconds s2 q)
    (sub2, checks2) = wlp pconds s1 sub1
  in (sub2, checks1 ++ checks2)
--In this case, we must check that our invariant holds, so we generate our checks
wlp pconds (Loop invar guard body) q = let
    (subWLP, subConds) = wlp pconds body invar
  in (invar, [
      BinOp (BinOp invar LAnd (LNot guard)) Implies q
      ,BinOp (BinOp invar LAnd guard) Implies subWLP ]
     ++ subConds)
wlp pconds (Var vars s) q = wlp pconds s q --TODO credentials 

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

programWLP :: PostConds -> Program -> (Expression, [Expression])
programWLP postConds (Program name params body) =
  let
    --Get our postcondition from the dictionary
    q = postConds Map.! name
    --Declare our parameters as variables
    s = Var params body
  in wlp postConds s q





