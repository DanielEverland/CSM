// This script implements our interactive calculator

// We need to import a couple of modules, including the generated lexer and parser
#r "bin/fslex/FsLexYacc.Runtime.dll"

open FSharp.Text.Lexing
open System
#load "Task1TypesAST.fs"
open Task1TypesAST
#load "Task1Parser.fs"
open Task1Parser
#load "Task1Lexer.fs"
open Task1Lexer

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)
let rec aeval e =
  match e with
    | Num(x) -> x
    | TimesExpr(x,y)        -> aeval(x) * aeval (y)
    | DivExpr(x,y)          -> aeval(x) / aeval (y)
    | PlusExpr(x,y)         -> aeval(x) + aeval (y)
    | MinusExpr(x,y)        -> aeval(x) - aeval (y)
    | PowExpr(x,y)          -> aeval(x) ** aeval (y)
    | UPlusExpr(x)          -> aeval(x)
    | UMinusExpr(x)         -> - aeval(x)
    | ParAExpr(x)            -> ( aeval(x) )
and beval e =
  match e with
    | True                  -> true
    | False                 -> false
    | SAnd(x, y)            -> beval(x) && beval(y)
    | SOr(x, y)             -> beval(x) || beval(y)
    | Neg(x)                -> not (beval(x))
    | Equal(x, y)           -> aeval(x) = aeval(y)
    | NEqual(x, y)          -> aeval(x) <> aeval(y)
    | Greater(x, y)         -> aeval(x) > aeval(y)
    | GreaterEqual(x, y)    -> aeval(x) >= aeval(y)
    | Less(x, y)            -> aeval(x) < aeval(y)
    | LessEqual(x, y)       -> aeval(x) <= aeval(y)
    | ParBExpr(x)            -> ( beval(x) )
and gceval e =
  match e with
    | BooleanGuard(x, y)    -> if beval(x) then ceval(y)
    | GCommands(x, y)       -> gceval(x)
                               gceval(y)
and ceval e =
  match e with
    | Commands(x, y)        -> ceval(x)
                               ceval(y)
    |IfStatement(x)         -> gceval(x) //????
    |DoStatement(x)         -> gceval(x) //????
//Don't know how to evaluate variables, skip and arrays or assign expressions

// We
let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = Task1Parser.start Task1Lexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res

// We implement here the function that interacts with the user
let rec compute n =
    if n = 0 then
        printfn "Bye bye"
    else
        printf "Enter an arithmetic expression: "
        try
        // We parse the input string
        let e = parse (Console.ReadLine())
        // and print the result of evaluating it        
        
        compute n
        with err -> compute (n-1)

// Start interacting with the user
compute 3
