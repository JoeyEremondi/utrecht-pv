module WLP where

import           Types
import           Z3Utils
import           Data.Data
import           Data.Generics
import           Data.List     (sort)
import qualified Data.Map      as Map

--trace _ x = x

--Constants limiting how far we go trying to infer loop invariants

fixpointDepth :: Int
fixpointDepth = 10

unrollDepth :: Int
unrollDepth = 20

{-
Helper function to get the names of variables in an assignment
-}
getVarTargets :: [AssignTarget] -> [Name]
getVarTargets targets =
  concatMap (\t -> case t of
                VarTarget n -> [n]
                _ -> []) targets

{-
Helper function to get array name/index pairs in an assignment
-}
getArrTargets :: [AssignTarget] -> [(Name, Expression)]
getArrTargets targets =
  concatMap (\t -> case t of
                ArrTarget n i -> [(n, i)]
                _ -> []) targets

{-
Given postconditions for each possible function called,
Parameter types for each possible function called,
the "top-level" statement we're finding the WLP for,
a "current" statement, and an expression,
find the weakest condition which will imply the postcondition
whenever the statement halts.

We need the postconditions in order to allow function calls, since inferring
Function postconditions is equivalent to inferring loop invariants, if we allow recursion

We need the "top-level" statement to get its free vars, since Z3 is used
to try to find loop invariants in this procedure.
-}
wlp :: (PostConds, ProgParams, Statement)  -> Statement -> Expression -> (Expression, [Expression])
wlp pconds  Skip q = (q, [])
wlp pconds (Assert p) q = (BinOp p LAnd q, [])
wlp pconds (Assume p) q = (BinOp p Implies q, [])
wlp pconds (Assign targets exp) q =
  let
    sub1 = subExpForName (getVarTargets targets) exp q
    sub2 = subExpForArrName (getArrTargets targets) exp sub1
  in (sub2, []) 
wlp pconds (Return expr) q = wlp pconds (Assign [VarTarget $ ToName "return"] expr) q 
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
wlp pconds (Loop Nothing guard body) q =
    case (tryFindingInvar pconds guard body q) of
      Nothing -> wlp pconds (unrollLoop guard body) q
      Just invar ->
        let
          (subWLP, subConds) = wlp pconds body invar
        in (invar,
            [
                (invar `land` (LNot guard)) `implies` q
               , (invar `land` guard) `implies` subWLP ] ++ subConds)

wlp pconds (Var vars s) q = wlp pconds s q

{-
Test if a given name occurs as a free variable in an expression
Used to resolve naming issues with foralls
-}
occursIn :: Name -> Expression -> Bool
occursIn n (IntLit e) = False
occursIn n (BoolLit e) = False
occursIn n (EName e) = e == n
occursIn n (BinOp e1 e2 e3) = (occursIn n e1) || (occursIn n e3)
occursIn n (LNot e) = occursIn n e
occursIn n (UninterpCall e1 e2) = (not . null) $ filter (== True) $ map (occursIn n) e2
occursIn n (Forall (n1, _) e2) = (n /= n1) && (occursIn n e2) --Exclude the bound variable
occursIn n (ArrAccess e1 e2) = (e1 == n) || (occursIn n e2)
occursIn n (IfThenElse e1 e2 e3) = (occursIn n e1) || (occursIn n e2) || (occursIn n e3)
occursIn n (RepBy e1 e2 e3) = (occursIn n e1) || (occursIn n e2) || (occursIn n e3)

{-
Given a set of names to replace, an expression to replace them with,
and an expression e, check if e is a name in our list,
and if it is, replace it with the given substitution
-}
subOneLevel :: [Name] ->  Expression -> Expression -> Expression
subOneLevel names subExp e@(EName varName)   =
  if (varName `elem` names)
  then subExp
  else e
--subOneLevel names subExp e@(Forall _ _) = fixForall subExp e 
subOneLevel _ _ e = e

{-
Rename variables in a Forall expression that conflict with the given expression
which is about to be substituted.
Fixes the problems with assignment subsitution conflicting with foralls.
-}
fixForall :: Expression -> Expression -> Expression
fixForall subExp e = 
 case e of
  Forall (vn, vt) body ->
    if vn `occursIn` subExp
       --Recursively call to make sure our new name isn't also in the list
    then
      let
         genNewName n = 
           if n `occursIn` subExp
              then genNewName (ToName $ "freshVar" ++ fromName n)
              else n
         newName = genNewName vn
         newBody = subExpForName [vn] (EName newName) body
         ret = Forall (newName, vt) newBody
       in ret 
    else e 
  _ -> e

{-
Use Scrap-Your-Boilerplate to recursively apply our substutitions
to our expression, bottom-up
-}
subExpForName ::  [Name] -> Expression -> Expression -> Expression
subExpForName names subExp  = let
    subAll = everywhere (mkT $ subOneLevel names subExp)
    fixAllForalls = everywhere (mkT $ fixForall subExp )
  in (subAll . fixAllForalls)
{-
Given a list of array names and index expressions, an expression to subtitute,
and an expression e, check if e is an array name in our list,
and if it is, replace it with the approprate RepBy expression
to denote a substitution
-}
subOneLevelArr :: [(Name, Expression)] -> Expression -> Expression -> Expression
subOneLevelArr nameIndexPairs subExpr e@(EName varName) =
   let
    nameIndList = filter (\(n,_) -> n == varName) nameIndexPairs
  in foldr (\(_,i) expSoFar -> RepBy expSoFar i subExpr) e nameIndList
subOneLevelArr l subExp e = e

{-
Use Scrap-Your-Boilerplate to recursively apply our substutitions
to our expression, bottom-up
-}
subExpForArrName :: (Data a) => [(Name, Expression)] -> Expression -> a -> a
subExpForArrName names subExp = let
    subAll = everywhere  (mkT $ subOneLevelArr names subExp)
    fixAllForalls = everywhere (mkT $ fixForall subExp )
  in (subAll . fixAllForalls)

{-
Given a loop guard and body, unroll the loop
a constant number of times
Used when we can't find a fixed-point invariant
-}
unrollLoop :: Expression -> Statement -> Statement
unrollLoop guard body = helper unrollDepth (Assert $ LNot guard)
  where
    helper 0 accum = accum
    helper i accum = helper (i-1) $
      ifelse guard
        (body `Seq` accum ) (Skip)


{-
Given program postconditions and parameters (for a multi-function program), a top-level statement,
a loop guard and body, and a post-condition, use fixpoint iteration,
up to a constant number of iterations,
to try to infer an invariant for the loop

The top-level statement is used to find free variables and their types
for generating a Z3 expression.
The Z3 program is invoked to test if two conditions are "equal"
-}
tryFindingInvar :: (PostConds, ProgParams, Statement) -> Expression -> Statement -> Expression -> Maybe Expression
tryFindingInvar pconds@(_,_,topLevelStmt) guard body postCond =
  let
    f w =  ( guard `land` (fst $ wlp pconds body w)) `lor` ((LNot guard) `land` postCond)
    iter w n = if (z3iff topLevelStmt (simplifyPred w) (simplifyPred (f w)))
               then (Just w)
               else if (n >= fixpointDepth)
               then Nothing
               else iter (f w) (n+1)
  in iter (BoolLit True) 0



{-
Apply some heuristics, putting predicates in a regular form
and simplify easy cases, so that our fix-point is likely to converge sooner,
and so that it won't get too large in size
-}
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

{-
Use SYB to apply our simplification rules bottom-up
on a whole expression
-}
simplifyPred :: Expression -> Expression
simplifyPred = everywhere $ mkT simplifyOneLevelPred

--Rules for which binary-operations can switch their arguments
isCommutative op = op `elem` [Plus, Times, And, Or, LAnd, LOr, Eq]

{-
Find the WLP for a particular function (program),
given post-conditions for all programs, and parameter types for all programs
-}
programWLP :: (PostConds, ProgParams) -> Program -> (Expression, [Expression])
programWLP (postConds, paramDict) (Program name params body _returnType) =
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


{-
Generate the Z3 code checking if the given statement matches the given post-condition
We do this by negating the proposition, then checkign if it is satisfiable.
First we search for all free-variables in the program, so that we can
declare them in our Z3 string.
-}
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





