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

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)
let rec aeval e (var : Map<string, int>, arr : Map<string, int[]>) : int =
  match e with
    | Num(x)                -> x
    | Var(x)                ->  match Map.tryFind x var with
                                | Some value -> value
                                | None -> 0
                                            // failwith (sprintf "No variable with name %s exists." x)
    | Array(x,y)            ->  match Array.tryFindIndex (fun elm -> elm = aeval y (var, arr)) (Map.find x arr) with
                                | Some value -> value
                                | None -> 0
                                            // failwith (sprintf "Index %f not found." (aeval y (var, arr)))
    | TimesExpr(x,y)        -> aeval x (var, arr) * aeval y (var, arr)
    | DivExpr(x,y)          -> int(aeval x (var, arr) / aeval y (var, arr))
    | PlusExpr(x,y)         -> aeval x (var, arr) + aeval y (var, arr)
    | MinusExpr(x,y)        -> aeval x (var, arr) - aeval y (var, arr)
    | PowExpr(x,y)          -> int(float(aeval x (var, arr)) ** float(aeval y (var, arr)))
    | UPlusExpr(x)          -> aeval x (var, arr)
    | UMinusExpr(x)         -> -aeval x (var, arr)
    | ParAExpr(x)           -> aeval x (var, arr)
and beval e (var : Map<string, int>, arr : Map<string, int[]>) =
  match e with
    | True                  -> true
    | False                 -> false
    | And(x, y)             ->  let lhs = beval x (var, arr)
                                let rhs = beval y (var, arr)
                                lhs && rhs
    | Or(x, y)              ->  let lhs = beval x (var, arr)
                                let rhs = beval y (var, arr)
                                lhs || rhs
    | SAnd(x, y)            -> beval x (var, arr) && beval y (var, arr)
    | SOr(x, y)             -> beval x (var, arr) || beval y (var, arr)
    | Neg(x)                -> not (beval x (var, arr))
    | Equal(x, y)           -> aeval x (var, arr) = aeval y (var, arr)
    | NEqual(x, y)          -> aeval x (var, arr) <> aeval y (var, arr)
    | Greater(x, y)         -> aeval x (var, arr) > aeval y (var, arr)
    | GreaterEqual(x, y)    -> aeval x (var, arr) >= aeval y (var, arr)
    | Less(x, y)            -> aeval x (var, arr) < aeval y (var, arr)
    | LessEqual(x, y)       -> aeval x (var, arr) <= aeval y (var, arr)
    | ParBExpr(x)           -> beval x (var, arr)
and gceval e (var, arr) =
  match e with
    | BooleanGuard(x, y)    -> if beval x (var, arr)
                               then ceval y (var, arr)
                               else (var, arr)
    | GCommands(x, y)       -> let (var1, arr1) = gceval x (var, arr)
                               gceval y (var1, arr1)
and ceval e (var : Map<string, int>, arr : Map<string, int[]>) : Map<string, int> * Map<string, int[]> =
  match e with
    | Commands(x, y)        -> let (var1, arr1) = ceval x (var, arr)
                               ceval y (var1, arr1)
    | IfStatement(x)        -> gceval x (var, arr)
    | DoStatement(x)        -> gceval x (var, arr)
    | AssignExpr(x, y)      -> (var.Add (x, aeval y (var, arr)), arr)
    | AssignArray(x, y, z)  -> let arr1 = Map.find x arr
                               arr1.[int(aeval y (var, arr))] <- aeval z (var, arr)
                               (var, arr.Add (x, arr1))
    | Skip                  -> (var, arr)

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

(*
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
*)

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
    // try
    let c = parse (Console.ReadLine())
    let (var, arr) = ceval c (Map.empty, Map.empty)

    let s = Map.fold (fun state n s -> state + string n + " " + string s + "\n") "" var
    printfn "%s" s

    // printfn "Map of variables: %M" var

    // let edges = edgesC Start End c
    // printfn "List of edges: %A" edges

    (*
    printfn "digraph program_graph {rankdir=LR;"
    printfn "node [shape = circle]; qS;"
    printfn "node [shape = doublecircle]; qE;"
    printfn "node [shape = circle]"
    printfn "%s" (printEdges edges)
    printfn "}"
    *)

    // and print the result of evaluating it        
    //printfn "Result: \n%s" (ceval c 0)

    // with err -> printf "Couldn't parse program"

// Start interacting with the user
compute
