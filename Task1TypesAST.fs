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
    with override this.ToString() =
                match this with
                | Num v -> v.ToString()
                | Var s -> s
                | Array (s, expr)    -> s + "[" + expr.ToString() + "]"
                | TimesExpr (a, b)   -> a.ToString() + "*" + b.ToString()
                | DivExpr (a, b)     -> a.ToString() + "/" + b.ToString()
                | PlusExpr (a, b)    -> a.ToString() + "+" + b.ToString()
                | MinusExpr (a, b)   -> a.ToString() + "-" + b.ToString()
                | PowExpr (a, b)     -> a.ToString() + "^" + b.ToString()
                | UPlusExpr v     -> v.ToString()
                | UMinusExpr v    -> "-" + v.ToString()
                | ParAExpr expr   -> "(" + expr.ToString() + ")"

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
    with override this.ToString() =
                match this with
                | True        -> "True"
                | False       -> "False"
                | And (a, b)    -> a.ToString() + "&" + b.ToString()
                | Or (a, b)     -> a.ToString() + "|" + b.ToString()
                | SAnd (a, b)   -> a.ToString() + "&&" + b.ToString()
                | SOr (a, b)    -> a.ToString() + "||" + b.ToString()
                | Neg e       -> "!" + e.ToString()
                | Equal (a, b)   -> a.ToString() + "=" + b.ToString()
                | NEqual (a, b)  -> a.ToString() + "!=" + b.ToString()
                | Greater (a, b) -> a.ToString() + ">" + b.ToString()
                | GreaterEqual (a, b)    -> a.ToString() + ">=" + b.ToString()
                | Less (a, b)    -> a.ToString() + "<" + b.ToString()
                | LessEqual (a, b)   -> a.ToString() + "<=" + b.ToString()
                | ParBExpr e  -> "(" + e.ToString() + ")"

type gcommand =
    | BooleanGuard of (bexpr * command)
    | GCommands of (gcommand * gcommand)
    with override this.ToString() =
                  match this with
                  | BooleanGuard (b, _) -> b.ToString()
                  | GCommands (_, _) -> "GCommands"
and command =
    | AssignExpr of (string * aexpr)
    | AssignArray of (string * aexpr * aexpr)
    | Skip
    | Commands of (command * command)
    | IfStatement of (gcommand)
    | DoStatement of (gcommand)
    with override this.ToString() =
                  match this with
                  | AssignExpr (varName, expr) -> varName + ":=" + expr.ToString()
                  | AssignArray (arrName, arrIndex, value) -> arrName + "[" + arrIndex.ToString() + "]:=" + value.ToString()
                  | Skip -> "Skip"
                  | Commands (a, b) -> "Commands"
                  | IfStatement gComm -> gComm.ToString()
                  | DoStatement gComm -> gComm.ToString()