{-
Joseph Eremondi
Program Verification
UU# 4229924
March 4, 2015
-}

--Common types used by all other modules

{-# LANGUAGE DeriveDataTypeable #-}
module Types where

import Data.Data

import qualified Data.Map as Map


--Type definitions
--Are straightforward from the assignment description, with a few deviants

--Just like in the assignment, but we also add a return type
data Program = Program ProgramName Parameters Statement Type


data Statement =
  Skip
  | Assert Expression
  | Assume Expression
  | Assign AssignTargets Expression
  | FnCallAssign AssignTarget ProgramName [Expression] --We needed to add this case for program calls
  | Return Expression
  | Seq Statement Statement
  | NonDet Statement Statement
  | Loop (Maybe Expression) Expression Statement
  | Var Variables Statement
    deriving (Eq, Ord, Data, Typeable)

type Parameters = [Variable]


data Variable = Variable [Credential] Name Type
              deriving (Eq, Ord, Data, Typeable)

type BoundVariable =(Name, Type)
                   

data Credential = Credential --I didn't implement this question, so it's just a unit type
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
    | UninterpCall String [Expression]
    | Forall BoundVariable Expression
    | ArrAccess ArrName Expression
    | IfThenElse Expression Expression Expression
    | RepBy Expression Expression Expression --This should only be used internally, for array expressions 
      deriving (Eq, Ord, Data, Typeable)

newtype Name = ToName {fromName :: String}
               deriving (Eq, Ord, Data, Typeable)

instance Show Name where
  show = fromName



                        
type ArrName = Name
         
newtype ProgramName = ToProgName {fromProgName :: String}
                      deriving (Eq, Ord, Data, Typeable)

data BinaryOp = Plus | Minus | Times | Div | Or | And | LOr | LAnd | Implies | Lt | Leq | Gt | Geq | Eq
    deriving (Eq, Ord, Data, Typeable)

data Type = Type PrimitiveType | ArrayType PrimitiveType
                                 deriving (Eq, Ord, Data, Typeable)

data PrimitiveType = IntT | BoolT
                            deriving (Eq, Ord, Data, Typeable)


type Variables = [Variable]
type Expressions = [Expression]
type AssignTargets = [AssignTarget]

--PostConditions are a dictionary mapping program names to an expression postcondition
type PostConds = Map.Map ProgramName Expression
--A dictionary mapping program names to their input parameters
type ProgParams = Map.Map ProgramName Parameters 
