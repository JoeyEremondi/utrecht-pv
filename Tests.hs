--module Tests where

import WLP
import Z3Utils
import Control.Monad (forM)
import System.Process (readProcessWithExitCode)
import System.Exit
import Data.Maybe (isJust)
import qualified Data.Map as Map


--TODO doc
data TestCase = SingleProgram (String, ExpectedResult, (Statement, Expression))
                | MultiProgram (String, ExpectedResult, [Program], PostConds)

data ExpectedResult = Succeed  | Fail

data TestResult = TestSuccess | TestFail String 

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

testList :: [TestCase]
testList = [
           simpleAssignTest
           , ifElseTest
           , loopMultTest
           , isSorted
           , badInvariantTest
           , ifElseBadTest
           , loopMultBadTest
           ]


getModel :: String -> IO String
getModel checkFile = do
  (_code, stdout, _stderr) <- readProcessWithExitCode "z3" ["-in"] (checkFile ++ "\n(get-model)")
  return stdout

combineResults :: TestResult -> TestResult -> TestResult
combineResults TestSuccess x = x
combineResults x TestSuccess = x
combineResults (TestFail s1) (TestFail s2) = TestFail (s1 ++ "\n" ++ s2)

multiUnsat :: ([Program], PostConds) -> IO TestResult
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
      (code, stdout, stderr) <- readProcessWithExitCode "z3" ["-in"] checkFile
      model <- getModel checkFile
      case (code, stdout, stderr) of
        (ExitSuccess, "unsat\n", "") -> return Nothing
        (ExitSuccess, "sat\n", "") ->
          return $ Just $ "Invariant Failed:\n" ++ checkFile ++ "\nModel:\n" ++ model
        r -> error $ "Z3 error: " ++ (show r) ++ "\n" ++ checkFile
  case (filter isJust invarPasses) of --TODO get justs
    ((Just str):_) -> return $ TestFail str
    [] -> do
      (code, stdout, stderr) <- readProcessWithExitCode "z3" ["-in"]  testFile
      model <- getModel testFile
      case ( code, stdout, stderr) of
        (ExitSuccess, "unsat\n", "") -> return TestSuccess
        (ExitSuccess, "sat\n", "") ->
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
  
