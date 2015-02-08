module A1 where

data Program = Program ProgramName Parameters Statement

data Statement =
  Skip
  | Assert Expression
  | Assume Expression
  | Assign AssignTargets Expressions
  | Return Expression
  | Seq Statement Statement
  | Loop Expression Expression Statement
  | Var Variables Statement

type Parameters = [Variable]
data Variable = Variable [Credential] Name Type

data BoundVariable = BoundVariable Name Type

data Credential = Credential --TODO optional?

data AssignTarget =
  VarTarget Name
  | ArrTarget ArrName Expression

data Expression =
    Lit
    | EName Name
    | BinOp Expression BinaryOp Expression
    | LNot Expression
    | FunctionCall -- TODO this case
    | Forall BoundVariable Expression
    | ArrAcess Name Expression
    | Arrow Expression Expression

newtype Name = ToName {fromName :: String}
newtype ArrName = ToArrName {fromArrName :: String}
newtype ProgramName = ToProgName {fromProgName :: String}

data BinaryOp = Plus | Minus | Times | Div | Or | And | LOr | LAnd | Implies | Lt | Leq | Gt | Geq | Eq

data Type = Type PrimitiveType | ArrType ArrayType

data PrimitiveType = IntT | BoolT

data ArrayType = ArrayType PrimitiveType

type Variables = [Variable]
type Expressions = [Expression]
type AssignTargets = [AssignTarget]

main = do
  putStrLn "TODO implement examples/tests"
