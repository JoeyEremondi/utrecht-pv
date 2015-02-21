--module Tests where

import WLP
import Z3Utils
import Control.Monad (forM)
import System.Process (readProcessWithExitCode)
import System.Exit

--String for filename to write to
--Bool for if the test should succeed
--And the program and postcondition to verify
type TestCase = (String, Bool, (Statement, Expression))


isSorted :: TestCase
isSorted = ("isSorted.z3", True, (s,q))
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
simpleAssignTest = ("simpleAssign.z3", True, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        "x" `assign` (IntLit 3 `plus` IntLit 4)
    q = ((var "x") `eq` IntLit 7)

ifElseTest :: TestCase
ifElseTest = ("ifElse.z3", True, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        ifelse (var "x" `lt` IntLit 0)
          ("x" `assign` IntLit 0)
        Skip
    q = (var "x" `geq` IntLit 0)

loopMultTest :: TestCase
loopMultTest = ("loopMult.z3", True, (s,q))
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
        
     

testList :: [TestCase]
testList = [
           simpleAssignTest
           , ifElseTest
           , loopMultTest
           , isSorted
           ]

   

main :: IO ()
main = do
  forM testList $ \(outFile, shouldPass, testCase) -> do
    let (testFile, checkFiles) = z3wlp testCase
    writeFile ("z3files/" ++ outFile) testFile
    
    --Check each invariant condition generated along the way
    forM checkFiles $ \checkFile -> do
      (code, stdout, stderr) <- readProcessWithExitCode "z3" ["-in"] checkFile
      case (code, stdout, stderr) of
        (ExitSuccess, "unsat\n", "") -> return ()
        r -> putStrLn $ "Bad Invariant " ++ (show r) ++ "\n" ++ checkFile

    --If all the invariants are valid, check the wlp itself
    (code, stdout, stderr) <- readProcessWithExitCode "z3" ["-in"]  testFile 
    case (shouldPass, code, stdout, stderr) of
        (True, ExitSuccess, "unsat\n", "") -> return ()
        (False, ExitSuccess, "sat\n", "") -> return ()
        _ -> putStrLn $ "ERROR! Failed test\n" ++ "    " ++ show (outFile, shouldPass, code, stdout, stderr, testFile)
    
  putStrLn $ "Finished running " ++ (show $ length testList) ++ " tests"
  return ()
  
