{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
module WLP where

import Types
import Z3Utils

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate, sort)
import Debug.Trace (trace)

import Control.Monad (forM)
import qualified Data.Map as Map
import Debug.Trace (trace)



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
wlp :: (PostConds, ProgParams, Statement)  -> Statement -> Expression -> (Expression, [Expression])
wlp pconds  Skip q = (q, [])
wlp pconds (Assert p) q = (BinOp p LAnd q, [])
wlp pconds (Assume p) q = (BinOp p Implies q, [])
wlp pconds (Assign targets exp) q =
  let
    sub1 = subExpForName (getVarTargets targets) exp q
    sub2 = subExpForArrName (getArrTargets targets) exp sub1
  in (sub2, []) --TODO make simultaneous?
wlp pconds (Return expr) q = wlp pconds (Assign [VarTarget $ ToName "return"] expr) q --TODO special name?
wlp (postConds, progParams, _) (FnCallAssign target progName params) q =
  let
    targetExp = case target of
      VarTarget name -> EName name
      ArrTarget arrName expr -> ArrAccess arrName expr
    progPostcond = postConds Map.! progName
    paramNames = map (\(Variable _ name _) -> name)$ progParams Map.! progName
    paramPairs = zip paramNames params
    postCondWithParams = foldr
                         (\(pname, pexp) pcond  -> subExpForName [pname] pexp pcond)
                         progPostcond paramPairs
    postCondWithRet = subExpForName [ToName "return"] targetExp postCondWithParams
    
  in (BinOp postCondWithRet Implies q, [])
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
wlp pconds (Loop (Just invar) guard body) q = let
    (subWLP, subConds) = wlp pconds body invar
  in (invar, [
      BinOp (BinOp invar LAnd (LNot guard)) Implies q
      ,BinOp (BinOp invar LAnd guard) Implies subWLP ]
     ++ subConds)
wlp pconds (Loop Nothing guard body) q = let
    invar = case (tryFindingInvar pconds guard body q) of
      Nothing -> BoolLit False
      Just i -> i
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

fixpointDepth :: Int
fixpointDepth = 100

unrollDepth :: Int
unrollDepth = 20

tryFindingInvar :: (PostConds, ProgParams, Statement) -> Expression -> Statement -> Expression -> Maybe Expression
tryFindingInvar pconds guard body postCond =
  let
    f w = BinOp (BinOp guard LAnd (fst $ wlp pconds body w)) LOr (BinOp (LNot guard) LAnd postCond)
    iter w n = if ((simplifyPred w) == (simplifyPred (f w)) )
               then (Just w)
               else if (n >= fixpointDepth)
               then Nothing
               else iter (f w) (n+1)
  in iter (BoolLit True) 0

invarIter :: (PostConds, ProgParams, Statement) -> Expression -> Statement -> Expression -> Int -> Expression
invarIter pconds@(_,_,topLevelStmt) guard body postCond nmax =
  let
    f w = BinOp (BinOp guard LAnd (fst $ wlp pconds body w)) LOr (BinOp (LNot guard) LAnd postCond)
    iter w n = if (z3iff topLevelStmt (simplifyPred w) (simplifyPred (f w)))
               then w
               else if (n >= nmax)
               then simplifyPred (f w)
               else iter (f w) (n+1)
  in iter (BoolLit True) 0


--We sort our expressions so they come up to equality if they're commutatively equal
simplifyOneLevelPred :: Expression -> Expression
simplifyOneLevelPred (LNot (BoolLit True)) = BoolLit False
simplifyOneLevelPred (LNot (BoolLit False)) = BoolLit True
simplifyOneLevelPred (LNot (LNot e)) = e
simplifyOneLevelPred (LNot (BinOp e1 LOr e2)) = BinOp (LNot e1) LAnd (LNot e2)
simplifyOneLevelPred (LNot (BinOp e1 LOr e2)) = BinOp (LNot e1) LAnd (LNot e2)
simplifyOneLevelPred (BinOp (BoolLit True) LAnd e) = e 
simplifyOneLevelPred (BinOp e LAnd(BoolLit True)) =  e
simplifyOneLevelPred (BinOp (BoolLit False) LOr e) =  e
simplifyOneLevelPred (BinOp e LOr (BoolLit False)) =  e
simplifyOneLevelPred (BinOp (IntLit 0) Plus e) = e
simplifyOneLevelPred (BinOp e Plus (IntLit 0)) = e
simplifyOneLevelPred (BinOp (IntLit 1) Times e) = e
simplifyOneLevelPred (BinOp e Times (IntLit 1)) = e
simplifyOneLevelPred (BinOp (IntLit 0) Times _e) = IntLit 0
simplifyOneLevelPred (BinOp _e Times (IntLit 0)) = IntLit 0
simplifyOneLevelPred (BinOp e1 op e2) = let
    [ee1, ee2] = sort [e1, e2] 
  in if isCommutative op
  then BinOp ee1 op ee2
  else BinOp e1 op e2
simplifyOneLevelPred e = e

simplifyPred :: Expression -> Expression
simplifyPred = everywhere $ mkT simplifyOneLevelPred

isCommutative op = op `elem` [Plus, Times, And, Or, LAnd, LOr, Eq]

programWLP :: (PostConds, ProgParams) -> Program -> (Expression, [Expression])
programWLP (postConds, paramDict) (Program name params body) =
  let
    --Get our postcondition from the dictionary
    q = postConds Map.! name
    --Declare our parameters as variables
    s = Var params body
  in wlp (postConds, paramDict, s) s q


--Generate the Z3 code checking if the given statement matches the given post-condition
z3wlpSingle :: (Statement, Expression) -> (String, [String])
z3wlpSingle (s, q) =
  let
    varDecs vars = foldr (\v decs -> decs ++ "\n" ++ varDec v) "" vars
    (theWLP, conds)  = wlp (Map.empty, Map.empty, s) s q
    formatPred p = (varDecs (freeVars s) ++ "\n") ++ (formatZ3 $ p )
  in  (formatPred theWLP, map formatPred conds)


--Generate the Z3 code checking if the given statement matches the given post-condition
z3wlpMulti :: ([Program], (PostConds, ProgParams)) -> [(String, [String])]
z3wlpMulti (progs, postConds) =
  let
    
    varDecs vars = foldr (\v decs -> decs ++ "\n" ++ varDec v) "" vars
    wlpsAndConds  = map (programWLP postConds) progs
    progWlpConds = zip progs wlpsAndConds
    formatPred prog pred = (varDecs (progFreeVars prog) ++ "\n") ++ (formatZ3 $ pred )
    formattedPreds = map (\(prog, (theWLP, conds)) ->
                           (formatPred prog theWLP,  (map (formatPred prog) conds) ) ) progWlpConds
  in formattedPreds





