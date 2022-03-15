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
    | Num(x)                -> (string) x
    | Var(x)                -> "" + x
    | Array(x,y)            -> "" + x + "[" + aeval(y) + "]"
    | TimesExpr(x,y)        -> "" + aeval(x) + "*" + aeval (y)
    | DivExpr(x,y)          -> "" + aeval(x) + "/" + aeval (y)
    | PlusExpr(x,y)         -> "" + aeval(x) + "+" + aeval (y)
    | MinusExpr(x,y)        -> "" + aeval(x) + "-" + aeval (y)
    | PowExpr(x,y)          -> "" + aeval(x) + "**" + aeval (y)
    | UPlusExpr(x)          -> "" + aeval(x)
    | UMinusExpr(x)         -> "" + " -" + aeval(x)
    | ParAExpr(x)           -> "" + "(" + aeval(x) + ")"
and beval e =
  match e with
    | True                  -> "true"
    | False                 -> "false"
    | And(x, y)             -> "" + beval(x) + "&" + beval(y)
    | Or(x, y)              -> "" + beval(x) + "|" + beval(y)
    | SAnd(x, y)            -> "" + beval(x) + "&&" + beval(y)
    | SOr(x, y)             -> "" + beval(x) + "||" + beval(y)
    | Neg(x)                -> "" + "!" + (beval(x))
    | Equal(x, y)           -> "" + aeval(x) + "=" + aeval(y)
    | NEqual(x, y)          -> "" + aeval(x) + "<>" + aeval(y)
    | Greater(x, y)         -> "" + aeval(x) + ">" + aeval(y)
    | GreaterEqual(x, y)    -> "" + aeval(x) + ">=" + aeval(y)
    | Less(x, y)            -> "" + aeval(x) + "<" + aeval(y)
    | LessEqual(x, y)       -> "" + aeval(x) + "<=" + aeval(y)
    | ParBExpr(x)           -> "" + "(" + beval(x) + ")"
and gceval e =
  match e with
    | BooleanGuard(x, y)    -> "" + beval(x) + "\n" + ceval(y)
    | GCommands(x, y)       -> "" + gceval(x) + " \n[] " + gceval(y)
and ceval e =
  match e with
    | Commands(x, y)        -> "" + ceval(x) + " ; \n" + ceval(y)
    | IfStatement(x)        -> "" + gceval(x)
    | DoStatement(x)        -> "" + gceval(x)
    | AssignExpr(x, y)      -> "" + x + ":=" + aeval(y)
    | AssignArray(x, y, z)  -> "" + x + "[" + aeval(y) + "]" + ":=" + aeval(z)
    | Skip                  -> " skip "

type Node = | Start
            | End
            | Inter of int
            with override this.ToString() =
                    match this with
                    | Start   -> "qS"
                    | End     -> "qE"
                    | Inter x -> "q" + string x

let printEdge qFrom label qTo = qFrom.ToString() + " -> " + qTo.ToString() + " [label = \"" + label + "\"];"

let mutable n = 0

let getFresh q = match q with
                 | Start|Inter _ -> n <- n + 1
                                    Inter n
                 | End           -> failwith "qFrom can't be end node"

let doneGC = function
    | BooleanGuard(x,_)     -> "!(" + beval(x) + ")"
    | GCommands(x,y)        -> "(" + gceval(x) + ")&(" + gceval(y) + ")"

let rec edgesC qFrom qTo C =
    match C with
    | AssignExpr(x,y)       -> [(qFrom, x + ":=" + aeval y, qTo)]
    | AssignArray(x,y,z)    -> [(qFrom, x + "[" + aeval y + "]:=" + aeval z, qTo)]
    | Skip                  -> [(qFrom, "skip", qTo)]
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = edgesC qFrom q C1
                               let E2 = edgesC q qTo C2
                               E1 @ E2
    | IfStatement(GC)       -> edgesGC qFrom qTo GC
    | DoStatement(GC)       -> let b = doneGC GC
                               let E = edgesGC qFrom qFrom GC
                               E @ [(qFrom, b, qTo)]

and edgesGC qFrom qTo GC =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               let E = edgesC q qTo C
                               [(qFrom, beval b, q)] @ E
    | GCommands(gc1, gc2)   -> let E1 = edgesGC qFrom qTo gc1
                               let E2 = edgesGC qFrom qTo gc2
                               E1 @ E2


let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = Task1Parser.start Task1Lexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res

let rec printEdges = function
    | (qFrom, label, qTo)::[]   -> printEdge qFrom label qTo
    | (qFrom, label, qTo)::xs   -> printEdge qFrom label qTo + "\n" + printEdges xs
    | _                         -> ""

// We implement here the function that interacts with the user
let compute =
    printf "Enter an input program: "

    // We parse the input string
    try
    let c = parse (Console.ReadLine())       
    let edges = edgesC Start End c
    // printfn "List of edges: %A" edges

    printfn "digraph program_graph {rankdir=LR;"
    printfn "node [shape = circle]; qS;"
    printfn "node [shape = doublecircle]; qE;"
    printfn "node [shape = circle]"
    printfn "%s" (printEdges edges)
    printfn "}"

    // and print the result of evaluating it        
    //printfn "Result: \n%s" (ceval c 0)

    with err -> printf "Couldn't parse program"

// Start interacting with the user
compute
