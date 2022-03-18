// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module Task1TypesAST

type aexpr =
  | Num of int
  | Var of string
  | Array of (string * aexpr)
  | TimesExpr of (aexpr * aexpr)
  | DivExpr of (aexpr * aexpr)
  | PlusExpr of (aexpr * aexpr)
  | MinusExpr of (aexpr * aexpr)
  | PowExpr of (aexpr * aexpr)
  | UPlusExpr of (aexpr)
  | UMinusExpr of (aexpr)
  | ParAExpr of (aexpr)

type bexpr =
  | True
  | False
  | And of (bexpr * bexpr)
  | Or of (bexpr * bexpr)
  | SAnd of (bexpr * bexpr)
  | SOr of (bexpr * bexpr)
  | Neg of (bexpr)
  | Equal of (aexpr * aexpr)
  | NEqual of (aexpr * aexpr)
  | Greater of (aexpr * aexpr)
  | GreaterEqual of (aexpr * aexpr)
  | Less of (aexpr * aexpr)
  | LessEqual of (aexpr * aexpr)
  | ParBExpr of (bexpr)

type gcommand =
  | BooleanGuard of (bexpr * command)
  | GCommands of (gcommand * gcommand)
and command =
  | AssignExpr of (string * aexpr)
  | AssignArray of (string * aexpr * aexpr)
  | Skip
  | Commands of (command * command)
  | IfStatement of (gcommand)
  | DoStatement of (gcommand)

