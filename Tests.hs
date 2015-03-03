--module Tests where
import Prelude hiding (seq)

import WLP
import Z3Utils
import Types
import Control.Monad (forM)
--import System.Process (readProcessWithExitCode)
--import System.Exit
import Data.Maybe (isJust)
import qualified Data.Map as Map


--TODO doc
data TestCase = SingleProgram (String, ExpectedResult, (Statement, Expression))
                | MultiProgram (String, ExpectedResult, [Program], (PostConds, ProgParams))

data ExpectedResult = Succeed  | Fail

data TestResult = TestSuccess | TestFail String 

getParams = (\(Program name params _) -> (name, params))

isSorted :: TestCase
isSorted = SingleProgram ("isSorted.z3", Succeed, (s,q))
  where 
     s =
      Var [
        Variable [] (ToName "arr")  (ArrayType IntT),
        Variable [] (ToName "i") (Type IntT),
        Variable [] (ToName "isSorted") (Type BoolT),
        Variable [] (ToName "n") (Type IntT)
        ] $
      (Assume $ var "n" `gt` IntLit 1) `Seq`
      ("isSorted" `assign` (BoolLit True)) `Seq`
      ("i" `assign` (IntLit 0)) `Seq`
      while
      --Invariant
      ( ((var "i" `geq` IntLit 0) `land`
         (var "i" `lt` var "n") `land`
        (var "n" `gt` IntLit 1) ) `land`
        
        ( (var "isSorted") `iff`
        (Forall (ToName "j",Type IntT )
         (((var "j" `lt` (var "i")) `land`
           (var "j" `geq` IntLit 0)) `implies`
            (ArrAccess (ToName "arr") (var "j") `leq` ArrAccess (ToName "arr") (var "j" `plus` IntLit 1))
         ))
        )
      )
      --Loop guard
      ( (var "i") `lt` (var "n" `minus` IntLit 1))
        --Loop body
       (
         ( ifelse ((ArrAccess (ToName "arr") (var "i")) `leq`
                   (ArrAccess (ToName "arr") (var "i" `plus` IntLit 1)))
           (Skip)
           ("isSorted" `assign` (BoolLit False))
          ) `Seq`
        ("i" `assign` (var "i" `plus` IntLit 1)
        )
         )
     q = --postcondition
       ( 
        --((var "n" `gt` IntLit 1)) `land`
         ( (var "isSorted") `iff`
       (Forall (ToName "j", Type IntT) $
         ((var "j" `lt` (var "n" `minus` IntLit 1)) `land` (var "j" `geq` IntLit 0) ) `implies` (
         (ArrAccess (ToName "arr") (var "j")) `leq`
         (ArrAccess (ToName "arr") (var "j" `plus` IntLit 1)) 
         ) ) ) )

simpleAssignTest :: TestCase
simpleAssignTest = SingleProgram ("simpleAssign.z3", Succeed, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        "x" `assign` (IntLit 3 `plus` IntLit 4)
    q = ((var "x") `eq` IntLit 7)

ifElseTest :: TestCase
ifElseTest = SingleProgram ("ifElse.z3", Succeed, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        ifelse (var "x" `lt` IntLit 0)
          ("x" `assign` IntLit 0)
        Skip
    q = (var "x" `geq` IntLit 0)

ifElseBadTest :: TestCase
ifElseBadTest = SingleProgram ("ifElse.z3", Fail, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        ifelse (var "x" `lt` IntLit 0)
          ("x" `assign` IntLit 0)
        Skip
    q = (var "x" `gt` IntLit 0)

loopMultTest :: TestCase
loopMultTest = SingleProgram ("loopMult.z3", Succeed, (s,q))
  where
    s = Var [
      Variable [] (ToName "x") (Type IntT),
      Variable [] (ToName "y") (Type IntT),
      Variable [] (ToName "i") (Type IntT)] $
      ("x" `assign` IntLit 0) `Seq`
      ("i" `assign` IntLit 0) `Seq`
      (while
        --Invariant
        ( (var "i" `leq` IntLit 10) `land`
          (var "i" `geq` IntLit 0) `land`
          ((var "i" `eq` IntLit 0) `implies` (var "x" `eq` IntLit 0)) `land`
          (var "x" `eq` (var "i" `times` var "y")) )
        --Guard
        (var "i" `lt` IntLit 10)
        --Body
        ( ("x" `assign` ((var "x") `plus` (var "y")))  `Seq`
          ("i" `assign` (var "i" `plus` IntLit 1))) )
    q = (var "i" `eq` IntLit 10) `land`
      (var "x" `eq` (IntLit 10 `times` var "y")) 
        
loopMultBadTest :: TestCase
loopMultBadTest = SingleProgram ("loopMultBad.z3", Fail, (s,q))
  where
    s = Var [
      Variable [] (ToName "x") (Type IntT),
      Variable [] (ToName "y") (Type IntT),
      Variable [] (ToName "i") (Type IntT)] $
      ("x" `assign` IntLit 0) `Seq`
      ("i" `assign` IntLit 0) `Seq`
      (while
        --Invariant
        ( (var "i" `leq` IntLit 10) `land`
          (var "i" `geq` IntLit 0) `land`
          ((var "i" `eq` IntLit 0) `implies` (var "x" `eq` IntLit 0)) `land`
          (var "x" `eq` (var "i" `times` var "y")) )
        --Guard, has an off-by one error
        (var "i" `leq` IntLit 10)
        --Body
        ( ("x" `assign` ((var "x") `plus` (var "y")))  `Seq`
          ("i" `assign` (var "i" `plus` IntLit 1))) )
    q = (var "i" `eq` IntLit 10) `land`
      (var "x" `eq` (IntLit 10 `times` var "y")) 


badInvariantTest :: TestCase
badInvariantTest = SingleProgram ("loopMultBadInvar.z3", Fail, (s,q))
  where
    s = Var [
      Variable [] (ToName "x") (Type IntT),
      Variable [] (ToName "y") (Type IntT),
      Variable [] (ToName "i") (Type IntT)] $
      ("x" `assign` IntLit 0) `Seq`
      ("i" `assign` IntLit 0) `Seq`
      (while
        --Invariant wrong, should be i <= 10
        ( (var "i" `lt` IntLit 10) `land`
          (var "i" `geq` IntLit 0) `land`
          ((var "i" `eq` IntLit 0) `implies` (var "x" `eq` IntLit 0)) `land`
          (var "x" `eq` (var "i" `times` var "y")) )
        --Guard, has an off-by one error
        (var "i" `lt` IntLit 10)
        --Body
        ( ("x" `assign` ((var "x") `plus` (var "y")))  `Seq`
          ("i" `assign` (var "i" `plus` IntLit 1))) )
    q = (var "i" `eq` IntLit 10) `land`
      (var "x" `eq` (IntLit 10 `times` var "y"))

gcdTest :: TestCase
gcdTest =
  MultiProgram ("gcd.z3", Succeed, [modulo, gcd], (postconds, params))
  where
    params = Map.fromList $ map getParams [modulo, gcd]
    modulo = Program
             (ToProgName "modulo")
             [Variable [] (ToName "x") (Type IntT),
             Variable [] (ToName "m") (Type IntT)]
             (Return $ var "x" `minus` ((var "x" `divv` var "m") `times` var "m") )
    gcd = Program
          (ToProgName "gcd")
          [Variable [] (ToName "a") (Type IntT),
          Variable [] (ToName "b") (Type IntT)]
          (Var [Variable [] (ToName "modab") (Type IntT),
               Variable [] (ToName "sub") (Type IntT)] $
          (ifelse (var "b" `eq` IntLit 0)
            (Return $ var "a")
            ( (callFn "modab" "modulo" [var "a", var "b"])`Seq`
              (callFn "sub" "gcd" [var "a", var "modab"]) `Seq`
            (Return $ var "sub"))
          ) )
    postconds = Map.fromList [
      (ToProgName "modulo",
       (( (var "x" `divv` var "m") `times` var "m") `plus` var "return") `eq` var "x")
      ,
      (ToProgName "gcd",
       ( (var "b" `eq` IntLit 0) `implies` (var "return" `eq` var "a")) `land`
       (((var "a" `gt` var "b") `land` (var "a" `gt` IntLit 0) `land` (var "b" `gt` IntLit 0))
       `implies`(Forall (ToName "c", Type IntT)
        ( (((UninterpCall "mod" [var "a", var "c"]) `eq` IntLit 0) `land`
          ((UninterpCall "mod" [var "b", var "c"]) `eq` IntLit 0) `land`
          (var "c" `gt` IntLit 0)) `implies`
          (var "c" `leq` var "return")
        )))
        )
      ] --TODO fix

basicFnCallTest :: TestCase
basicFnCallTest =
  MultiProgram ("fnCallTest.z3", Succeed, [const3, mainF], (postconds, params))
  where
    const3 = Program (ToProgName "three") [Variable [] (ToName "x") (Type IntT)]
             (Return $ IntLit 3)
    mainF = Program (ToProgName "main") [] (
      Var [Variable [] (ToName "y") (Type IntT)] (
         (callFn "y" "three" [IntLit 0]) `Seq`
         (Return $ var "y")
         )
      )
    postconds = Map.fromList $ [
      (ToProgName "three", var "return" `eq` IntLit 3),
      (ToProgName "main", var "return" `eq` IntLit 3)
      ]
    params = Map.fromList $ map getParams [const3, mainF]


loopMultNoInvarTest :: TestCase
loopMultNoInvarTest = SingleProgram ("loopMult.z3", Succeed, (s,q))
  where
    s = Var [
      Variable [] (ToName "x") (Type IntT),
      Variable [] (ToName "y") (Type IntT),
      Variable [] (ToName "i") (Type IntT)] $
      ("x" `assign` IntLit 0) `Seq`
      ("i" `assign` IntLit 0) `Seq`
      (while_
        --Guard
        (var "i" `lt` IntLit 10)
        --Body
        ( ("x" `assign` ((var "x") `plus` (var "y")))  `Seq`
          ("i" `assign` (var "i" `plus` IntLit 1))) )
    q = (var "i" `eq` IntLit 10) `land`
      (var "x" `eq` (IntLit 10 `times` var "y")) 





testList :: [TestCase]
testList = [
           simpleAssignTest
           , ifElseTest
           , loopMultTest
           , isSorted
           , badInvariantTest
           , ifElseBadTest
           , loopMultBadTest
           , basicFnCallTest
           , gcdTest
            , loopMultNoInvarTest
           ]




combineResults :: TestResult -> TestResult -> TestResult
combineResults TestSuccess x = x
combineResults x TestSuccess = x
combineResults (TestFail s1) (TestFail s2) = TestFail (s1 ++ "\n" ++ s2)

multiUnsat :: ([Program], (PostConds, ProgParams)) -> IO TestResult
multiUnsat testCase = do
  results <- mapM z3Unsat (z3wlpMulti testCase)
  return $ foldr combineResults TestSuccess results

singleUnsat :: (Statement, Expression) -> IO TestResult
singleUnsat testCase = z3Unsat $ z3wlpSingle testCase 

z3Unsat :: (String, [String]) -> IO TestResult
z3Unsat (testFile, checkFiles) = do
  --Check each invariant condition generated along the way
  invarPasses <-
    forM checkFiles $ \checkFile -> do
      isValid <- z3IsValid checkFile
      model <- getModel checkFile
      case isValid of
        True -> return Nothing
        False ->
          return $ Just $ "Invariant Failed:\n" ++ checkFile ++ "\nModel:\n" ++ model
        r -> error $ "Z3 error: " ++ (show r) ++ "\n" ++ checkFile
  case (filter isJust invarPasses) of --TODO get justs
    ((Just str):_) -> return $ TestFail str
    [] -> do
      isValid <- z3IsValid testFile
      model <- getModel testFile
      case isValid of
        True -> return TestSuccess
        False ->
          return $ TestFail $ "Invalid Precondition:\n" ++ testFile ++ "\nModel:\n" ++ model
        r -> error $ "Z3 error: " ++ (show r) ++ "\n" ++ testFile
      








main :: IO ()
main = do
  --Get a list of bools for if each tests passes
  successList <- forM testList $ \test -> do
      satResult <- case test of
        SingleProgram (testName, shouldPass, testCase) -> singleUnsat testCase
        MultiProgram (testName, shouldPass, programs, postconds) -> multiUnsat (programs, postconds)
      let (testName, shouldPass) = case test of
            SingleProgram (n, s, _) -> (n,s)
            MultiProgram (n, s, _, _) -> (n,s)
      case (shouldPass, satResult) of
            (Succeed, TestSuccess) -> return True
            (Fail, TestFail _) -> return True
            (_, TestFail s) -> do
              putStrLn $ "FAILED: " ++ testName ++ " found counter-example\n    " ++ s
              return False
            (_, TestSuccess) -> do
              putStrLn $ "FAILED: " ++ testName ++ " could not disprove bad postcondition"
              return False
    
  let numPasses = length $ filter id successList
  let numFails = length $ filter not successList
  putStrLn $ "Tests passed: " ++ show numPasses
  putStrLn $ "Tests failed: " ++ show numFails
  return ()
  

