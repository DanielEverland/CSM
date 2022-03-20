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

type Node = | Start
            | End
            | Inter of int
            with override this.ToString() =
                    match this with
                    | Start   -> "qS"
                    | End     -> "qE"
                    | Inter x -> "q" + string x

type VariableData = Map<string, int>
type ArrayData = Map<string, int[]>
// The data we can modify during runtime
type RuntimeData = (VariableData * ArrayData)

// Lambdas that take the current runtime data, modify it and return new runtime data
type CompiledAction = RuntimeData -> RuntimeData

// An edge consists of an action and target node
type Edge = CompiledAction * Node

// A lookup table that determines the edges of all nodes
type Program = Map<Node, Edge list>

let getEdges qFrom T =
    match Map.tryFind qFrom T with
    | Some e -> e
    | None -> []

let merge (mapA : Program) (mapB : Program) = Map.fold (fun acc key value -> let edges = getEdges key acc
                                                                             Map.add key (value@edges) acc) mapA mapB

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)
let rec aeval e ((var, arr) : RuntimeData) : int =
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
and beval e ((var, arr) : RuntimeData) : bool =
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
and gceval e ((var, arr) : RuntimeData) : RuntimeData =
  match e with
    | BooleanGuard(x, y)    -> if beval x (var, arr)
                               then ceval y (var, arr)
                               else (var, arr)
    | GCommands(x, y)       -> let (var1, arr1) = gceval x (var, arr)
                               gceval y (var1, arr1)
and ceval e ((var, arr) : RuntimeData) : RuntimeData =
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

let printEdge qFrom label qTo = qFrom.ToString() + " -> " + qTo.ToString() + " [label = \"" + label + "\"];"

let mutable n = 0
let getFresh q = match q with
                 | Start|Inter _ -> n <- n + 1
                                    Inter n
                 | End           -> failwith "qFrom can't be end node"

//let doneGC = function
//    | BooleanGuard(x,_)     -> "!(" + beval(x) + ")"
//    | GCommands(x,y)        -> "(" + gceval(x) + ")&(" + gceval(y) + ")"

let rec edgesC (qFrom : Node) (qTo : Node) (C : command) (T : Program) : Program =
    match C with
    | AssignExpr(x,y)       -> Map.add qFrom (((fun runtimeData -> ceval (AssignExpr(x, y)) runtimeData), qTo)::(getEdges qFrom T)) T
    | AssignArray(x,y,z)    -> Map.add qFrom (((fun runtimeData -> ceval (AssignArray(x, y, z)) runtimeData), qTo)::(getEdges qFrom T)) T
    | Skip                  -> T
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = edgesC qFrom q C1 T
                               let E2 = edgesC q qTo C2 T
                               merge E1 E2
    | IfStatement(GC)       -> edgesGC qFrom qTo GC False T
    | DoStatement(GC)       -> let E1 = edgesGC qFrom qFrom GC False T
                               let E2 = Map.add qFrom (((fun runtimeData -> ceval (DoStatement(GC)) runtimeData), qTo)::(getEdges qFrom T)) T
                               merge E1 E2
and edgesGC (qFrom : Node) (qTo : Node) (GC : gcommand) (b : bexpr) (T : Program) : Program =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               let E = edgesC q qTo C T
                               Map.add qFrom (((fun runtimeData -> gceval (BooleanGuard(b, C)) runtimeData), q)::(getEdges qFrom T)) E
    | GCommands(gc1, gc2)   -> match determinism with
                                | false ->  let E1 = edgesGC qFrom qTo gc1 b T
                                            let E2 = edgesGC qFrom qTo gc2 b T
                                            merge E1 E2
                                | _     ->  match (gc1, gc2) with
                                            | (BooleanGuard(b1, c1), GCommands(gc2gc1, gc2gc3)) ->  let E1 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    let E2 = edgesGC qFrom qTo (GCommands(gc2gc1, gc2gc3)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    merge E1 E2
                                            | (GCommands(gc1, gc2), BooleanGuard(b1, c1))       ->  let E1 = edgesGC qFrom qTo (GCommands(gc1, gc2)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    let E2 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    merge E1 E2
                                            | (BooleanGuard(b1, c1), BooleanGuard(b2, c2)) ->       let E1 = edgesGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    let E2 = edgesGC qFrom qTo (BooleanGuard(And(b2, Neg(And(ParBExpr(b1), Neg(b)))), c1)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    merge E1 E2
                                            | _ ->  let E1 = edgesGC qFrom qTo gc1 b T
                                                    let E2 = edgesGC qFrom qTo gc2 b T
                                                    merge E1 E2

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

let getProgramGraphString program = Map.fold (fun state n edgeList -> state + string n + " -> " + (List.fold (fun state (_, toNode) -> (if state = "" then state else state + ", ") + string toNode) "" edgeList) + "\n") "" program

// We implement here the function that interacts with the user
let compute =
    printf "Enter an input program: "

    // We parse the input string
    // try
    let c = parse (Console.ReadLine())
    let program = edgesC Start End c Map.empty
    //let (var, arr) = ceval c (Map.empty, Map.empty)

    printfn "%s" (getProgramGraphString program)

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
