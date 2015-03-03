{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
module Types where

import Data.Data
import Data.Generics
import qualified Data.Set as Set
import Data.Typeable
import Data.List (intercalate, sort)
import Debug.Trace (trace)

import Control.Monad (forM)
import qualified Data.Map as Map
import Debug.Trace (trace)



data Program = Program ProgramName Parameters Statement


data Statement =
  Skip
  | Assert Expression
  | Assume Expression
  | Assign AssignTargets Expression
  | FnCallAssign AssignTarget ProgramName [Expression]
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
    | UninterpCall String [Expression]
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
type ProgParams = Map.Map ProgramName Parameters 
