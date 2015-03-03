--module Tests where
import           Prelude       hiding (seq)

import           Control.Monad (forM)
import qualified Data.Map      as Map
import           Data.Maybe    (isJust)
import           Types
import           WLP
import           Z3Utils


{-
A Test case: either a single program with a name, expected result, program and postcondition,
or a multi-function program, with name, expected result, a list of functions, and
dictionaries of their postconditions and parameters
-}
data TestCase = SingleProgram (String, ExpectedResult, (Statement, Expression))
                | MultiProgram (String, ExpectedResult, [Program], (PostConds, ProgParams))

{-
Self-explanatory: we annotate each test case with whether the program should
or shouldn't fulfill its postcondition
-}
data ExpectedResult = Succeed  | Fail

{-
The actual outcome of a Z3 test.
Either Z3 found no conunter-examples,
or it found a counter-example, and we give a string with some error information
-}
data TestResult = TestSuccess | TestFail String

{-
Helper util to get the name and parameters from a Program
-}
getParams :: Program -> (ProgramName, Parameters)
getParams = (\(Program name params _ _) -> (name, params))

{-
Check if an array is sorted or not.

The postcondition is that the variable isSorted is set to true
if and only if every element in the array range is less than
or equal to the element after it

-}
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

{-
Very simple case, x := 3 + 4, post condition is that x=7
-}
simpleAssignTest :: TestCase
simpleAssignTest = SingleProgram ("simpleAssign.z3", Succeed, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        "x" `assign` (IntLit 3 `plus` IntLit 4)
    q = ((var "x") `eq` IntLit 7)

{-
Very simple case with branching, Check if x is less than 0,
if it is, set it to 0.
Postcondition is that x >= 0
-}
ifElseTest :: TestCase
ifElseTest = SingleProgram ("ifElse.z3", Succeed, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        ifelse (var "x" `lt` IntLit 0)
          ("x" `assign` IntLit 0)
        Skip
    q = (var "x" `geq` IntLit 0)

{-
Like the above tests, but with a bad postcondition, asserting
that x > 0.
Z3 should find a counter-example showing that the program
does not meet its postcondition.
-}
ifElseBadTest :: TestCase
ifElseBadTest = SingleProgram ("ifElse.z3", Fail, (s,q))
  where
    s = Var [Variable [] (ToName "x") (Type IntT)] $
        ifelse (var "x" `lt` IntLit 0)
          ("x" `assign` IntLit 0)
        Skip
    q = (var "x" `gt` IntLit 0)

{-
Use iteration to set x to 10*y.
Post-condition is that x=10y.
-}
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

{-
Like the above test, but put an off-by-one error in the loop guard,
to make sure it doesn't still meet the postcondition.
-}
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

{-
Like the loopMult test, but we incorrectly annotate our loop
with an invariant.
Z3 should find that this invariant doesn't meet the conditions for soundness.
-}
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

{-
A test case showing the transformer work for multi-function programs.
We define a modulo function which calculates modulo using integer division.
We then prove the correctness of Euclid's recursive algorithm for finding the
greatest common divisor of two integers.

We assume that, of the input parameters a and b, a > b,
and both are non-negative.
-}
gcdTest :: TestCase
gcdTest =
  MultiProgram ("gcd.z3", Succeed, [modulo, gcdProg], (postconds, params))
  where
    params = Map.fromList $ map getParams [modulo, gcdProg]
    modulo = Program
             (ToProgName "modulo")
             [Variable [] (ToName "x") (Type IntT),
             Variable [] (ToName "m") (Type IntT)]
             (Return $ var "x" `minus` ((var "x" `divv` var "m") `times` var "m") ) (Type IntT)
    gcdProg = Program
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
          ) ) (Type IntT)
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
      ]

{-
Our GCD test, but where we mess up the definition and postcondition for modulo
-}
badGCDTest :: TestCase
badGCDTest =
  MultiProgram ("gcdBad.z3", Fail, [modulo, gcdProg], (postconds, params))
  where
    params = Map.fromList $ map getParams [modulo, gcdProg]
    modulo = Program
             (ToProgName "modulo")
             [Variable [] (ToName "x") (Type IntT),
             Variable [] (ToName "m") (Type IntT)]
             (Return $ IntLit 22 ) (Type IntT)
    gcdProg = Program
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
          ) ) (Type IntT)
    postconds = Map.fromList [
      (ToProgName "modulo",
       (var "return" `eq` IntLit 22))
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
      ]

{-
Make a function that returns 3, and check that it returns 3.
Extremely basic sanity check for multi-function programs.
-}
basicFnCallTest :: TestCase
basicFnCallTest =
  MultiProgram ("fnCallTest.z3", Succeed, [const3, mainF], (postconds, params)) 
  where
    const3 = Program (ToProgName "three") [Variable [] (ToName "x") (Type IntT)]
             (Return $ IntLit 3) (Type IntT)
    mainF = Program (ToProgName "main") [] (
      Var [Variable [] (ToName "y") (Type IntT)] (
         (callFn "y" "three" [IntLit 0]) `Seq`
         (Return $ var "y") 
         ) 
      ) (Type IntT)
    postconds = Map.fromList $ [
      (ToProgName "three", var "return" `eq` IntLit 3),
      (ToProgName "main", var "return" `eq` IntLit 3)
      ]
    params = Map.fromList $ map getParams [const3, mainF]

{-
Verify a program with a loop that is not annotated (this is what while_ indicates).
This is the example given in the slides.
-}
slidesNoInvarTest :: TestCase
slidesNoInvarTest = SingleProgram ("SlidesNoInvar", Succeed, (s,q))
  where
    s = Var [Variable [] (ToName "y") (Type IntT)]
      $ (Assume $ var "y" `gt` IntLit 0) `Seq`
        while_ (var "y" `gt` IntLit 0) ("y" `assign` (var "y" `minus` IntLit 1))
    q = var "y" `eq` IntLit 0

{-
Our integer multiplication program from above, with the loop precondition removed.
Since it always loops 10 times, our finite-unrolling succeeds here,
even though fixpoint iteration fails.
-}
unrollingWorksTest :: TestCase
unrollingWorksTest = SingleProgram ("unrollingWorks.z3", Succeed, (s,q))
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
    q = ((var "i" `eq` IntLit 10) `land`
      (var "x" `eq` (IntLit 10 `times` var "y")))

{-
Like the above tests, but we fail because our loop runs more times
than our unrolling accounts for, generating a badn invalid invariant.
-}
unrollingFailsTest :: TestCase
unrollingFailsTest = SingleProgram ("unrollFail.z3", Fail, (s,q))
  where
    s = Var [
      Variable [] (ToName "x") (Type IntT),
      Variable [] (ToName "y") (Type IntT),
      Variable [] (ToName "i") (Type IntT)] $
      ("x" `assign` IntLit 0) `Seq`
      ("i" `assign` IntLit 0) `Seq`
      (while_
        --Guard
        (var "i" `lt` IntLit 300)
        --Body
        ( ("x" `assign` ((var "x") `plus` (var "y")))  `Seq`
          ("i" `assign` (var "i" `plus` IntLit 1))) )
    q = ((var "i" `eq` IntLit 300) `land`
      (var "x" `eq` (IntLit 300 `times` var "y")))


--All tests to be run
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
           , slidesNoInvarTest
           , unrollingWorksTest
           , unrollingFailsTest
           , badGCDTest
           ]



{-
Used to determine whether, after testing multiple functions,
all were a success, or if some failed
-}
combineResults :: TestResult -> TestResult -> TestResult
combineResults TestSuccess x = x
combineResults x TestSuccess = x
combineResults (TestFail s1) (TestFail s2) = TestFail (s1 ++ "\n" ++ s2)

{-
Given a list of programs program, and dictionaries of their postconditions and parameters,
test if all programs meet their postconditions using Z3
-}
multiUnsat :: ([Program], (PostConds, ProgParams)) -> IO TestResult
multiUnsat testCase = do
  results <- mapM z3Unsat (z3wlpMulti testCase)
  return $ foldr combineResults TestSuccess results

{-
Use Z3 to test if a statement meets a given postcondition
-}
singleUnsat :: (Statement, Expression) -> IO TestResult
singleUnsat testCase = z3Unsat $ z3wlpSingle testCase

{-
Given the Z3 string of a program, and Z3 strings of each of its invariants,
check the invariants and the program, then combine them into a single result
-}
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
  case (filter isJust invarPasses) of
    ((Just str):_) -> return $ TestFail str
    [] -> do
      isValid <- z3IsValid testFile
      model <- getModel testFile
      case isValid of
        True -> return TestSuccess
        False ->
          return $ TestFail $ "Invalid Precondition:\n" ++ testFile ++ "\nModel:\n" ++ model
        r -> error $ "Z3 error: " ++ (show r) ++ "\n" ++ testFile





{-
Our main loop:
For each of our tests, call the appropriate function to invoke Z3,
and compare the result (succeed/fail) against the expected result.
If we don't get the expected result, print an error message
with information about what went wrong.
-}
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


