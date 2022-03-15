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

// ======================
// ======= CONFIG =======
// ======================
// Toggles whether a deterministic program graph is created
let determinism = true

let variables = Map.empty
let arrays = Map.empty

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)
let rec aeval e =
  match e with
    | Num(x)                -> x
    | Var(x)                ->  match Map.tryFind x variables with
                                | Some value -> value
                                | None -> failwith "No variable with name " + x + " exists."
    | Array(x,y)            ->  match List.tryFindIndex (fun elm -> elm = aeval(y)) (Map.find x arrays) with
                                | Some value -> value
                                | None -> failwith "Index " + aeval(y) + " not found."
    | TimesExpr(x,y)        -> aeval(x) * aeval(y)
    | DivExpr(x,y)          -> aeval(x) / aeval(y)
    | PlusExpr(x,y)         -> aeval(x) + aeval(y)
    | MinusExpr(x,y)        -> aeval(x) - aeval(y)
    | PowExpr(x,y)          -> aeval(x) ** aeval(y)
    | UPlusExpr(x)          -> aeval(x)
    | UMinusExpr(x)         -> -aeval(x)
    | ParAExpr(x)           -> aeval(x)
and beval e =
  match e with
    | True                  -> true
    | False                 -> false
    | And(x, y)             ->  let lhs = beval(x)
                                let rhs = beval(y)
                                lhs && rhs
    | Or(x, y)              ->  let lhs = beval(x)
                                let rhs = beval(y)
                                lhs || rhs
    | SAnd(x, y)            -> beval(x) && beval(y)
    | SOr(x, y)             -> beval(x) || beval(y)
    | Neg(x)                -> !beval(x)
    | Equal(x, y)           -> aeval(x) = aeval(y)
    | NEqual(x, y)          -> aeval(x) <> aeval(y)
    | Greater(x, y)         -> aeval(x) > aeval(y)
    | GreaterEqual(x, y)    -> aeval(x) >= aeval(y)
    | Less(x, y)            -> aeval(x) < aeval(y)
    | LessEqual(x, y)       -> aeval(x) <= aeval(y)
    | ParBExpr(x)           -> beval(x)
and gceval e =
  match e with
    | BooleanGuard(x, y)    -> if beval(x) then ceval(y)
    | GCommands(x, y)       ->  gceval(x)
                                gceval(y)
and ceval e =
  match e with
    | Commands(x, y)        ->  ceval(x)
                                ceval(y)
    | IfStatement(x)        -> gceval(x)
    | DoStatement(x)        -> gceval(x)
    | AssignExpr(x, y)      -> variables.Change (x, (fun elm =  match elm with
                                                                | Some -> aeval(y)
                                                                | None -> failwith "No variable with name " + x + " exists."))
    | AssignArray(x, y, z)  -> match List.tryFindIndex (fun elm -> elm = aeval(y)) (Map.find x arrays) with
                                | Some value -> value
                                | None -> failwith "Index " + aeval(y) + " not found."
    
    "" + x + "[" + aeval(y) + "]" + ":=" + aeval(z)
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
    | IfStatement(GC)       -> edgesGC qFrom qTo GC False
    | DoStatement(GC)       -> let b = doneGC GC
                               let E = edgesGC qFrom qFrom GC False
                               E @ [(qFrom, b, qTo)]

and edgesGC qFrom qTo GC b =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               let E = edgesC q qTo C
                               [(qFrom, beval b, q)] @ E
    | GCommands(gc1, gc2)   -> match determinism with
                                | false ->  let E1 = edgesGC qFrom qTo gc1 b
                                            let E2 = edgesGC qFrom qTo gc2 b
                                            E1 @ E2
                                | _     ->  match (gc1, gc2) with
                                            | (BooleanGuard(b1, c1), GCommands(gc2gc1, gc2gc3)) ->  let E1 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b
                                                                                                    let E2 = edgesGC qFrom qTo (GCommands(gc2gc1, gc2gc3)) (And(b, Neg(ParBExpr(b1))))
                                                                                                    E1 @ E2
                                            | (GCommands(gc1, gc2), BooleanGuard(b1, c1))       ->  let E1 = edgesGC qFrom qTo (GCommands(gc1, gc2)) (And(b, Neg(ParBExpr(b1))))
                                                                                                    let E2 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b
                                                                                                    E1 @ E2
                                            | (BooleanGuard(b1, c1), BooleanGuard(b2, c2)) ->       let E1 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b
                                                                                                    let E2 = edgesGC qFrom qTo (BooleanGuard(And(b2, Neg(And(ParBExpr(b1), Neg(b)))), c1)) (And(b, Neg(ParBExpr(b1))))
                                                                                                    E1 @ E2
                                            | _ ->  let E1 = edgesGC qFrom qTo gc1 b
                                                    let E2 = edgesGC qFrom qTo gc2 b
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
