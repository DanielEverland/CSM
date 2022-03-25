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
let debug = false

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

type EdgeViability = RuntimeData -> bexpr

// An edge consists of an action and target node
type Edge = CompiledAction * EdgeViability * Node

// A lookup table that determines the edges of all nodes
type Program = Map<Node, Edge list>

type ProgramState = (Node * RuntimeData * Program)

type Domain = Set<Node>
type SPFEdge = Node
type SPF = Map<Node, SPFEdge list>

let getEdges qFrom T =
    match Map.tryFind qFrom T with
    | Some e -> e
    | None -> []

let merge mapA mapB = Map.fold (fun acc key value -> let edges = getEdges key acc
                                                     Map.add key (value@edges) acc) mapA mapB

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)
let rec aeval e ((var, arr) : RuntimeData) : int =
  match e with
    | Num(x)                -> x
    | Var(x)                ->  match Map.tryFind x var with
                                | Some value -> value
                                | None -> failwith ("No data has been assigned to " + (x.ToString()))
    | Array(x,y)            ->  match Map.tryFind x arr with
                                | Some arrVal -> arrVal.[(aeval y (var, arr))]
                                | None -> failwith ("No array exists with the name " + (x.ToString()))
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
    | AssignExpr(x, y)      ->  if debug then printf "%s -> %d\n" x (aeval y (var, arr))
                                (var.Add (x, aeval y (var, arr)), arr)
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

let rec doneGC = function
    | BooleanGuard(x,_)     -> Neg(x)
    | GCommands(x,y)        -> Or((doneGC x), (doneGC y))

let rec edgesC (qFrom : Node) (qTo : Node) (C : command) (T : Program) : Program =
    match C with
    | AssignExpr(x,y)       -> Map.add qFrom (((fun runtimeData -> ceval (AssignExpr(x, y)) runtimeData), (fun runtimeData -> True), qTo)::(getEdges qFrom T)) T
    | AssignArray(x,y,z)    -> Map.add qFrom (((fun runtimeData -> ceval (AssignArray(x, y, z)) runtimeData), (fun runtimeData -> True), qTo)::(getEdges qFrom T)) T
    | Skip                  -> T
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = edgesC qFrom q C1 T
                               let E2 = edgesC q qTo C2 T
                               merge E1 E2
    | IfStatement(GC)       -> edgesGC qFrom qTo GC False T
    | DoStatement(GC)       -> let E1 = edgesGC qFrom qFrom GC False T
                               let E2 = Map.add qFrom (((fun runtimeData -> ceval (DoStatement(GC)) runtimeData), (fun runtimeData -> doneGC GC), qTo)::(getEdges qFrom T)) T
                               merge E1 E2
and edgesGC (qFrom : Node) (qTo : Node) (GC : gcommand) (b : bexpr) (T : Program) : Program =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               let E = edgesC q qTo C T
                               Map.add qFrom (((fun runtimeData -> runtimeData), (fun runtimeData -> b), q)::(getEdges qFrom T)) E
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
                                                                                                    let E2 = edgesGC qFrom qTo (BooleanGuard(And(b2, Neg(And(ParBExpr(b1), Neg(b)))), c2)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    merge E1 E2
                                            | _ ->  let E1 = edgesGC qFrom qTo gc1 b T
                                                    let E2 = edgesGC qFrom qTo gc2 b T
                                                    merge E1 E2

let rec domC (qFrom : Node) (qTo : Node) (C : command) (D : Domain) : Domain =
    match C with
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = domC qFrom q C1 D
                               let E2 = domC q qTo C2 D
                               Set.union E1 E2
    | IfStatement(GC)       -> domGC qFrom qTo GC False D
    | DoStatement(GC)       -> let E1 = domGC qFrom qFrom GC False D
                               let E2 = Set.add qFrom D
                               Set.union E1 E2
    | _ -> D
and domGC (qFrom : Node) (qTo : Node) (GC : gcommand) (b : bexpr) (D : Domain) : Domain =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               domC q qTo C D
    | GCommands(gc1, gc2)   -> let E1 = domGC qFrom qTo gc1 b D
                               let E2 = domGC qFrom qTo gc2 b D
                               Set.union E1 E2

let rec spfC (qFrom : Node) (qTo : Node) (C : command) (T : SPF) : SPF =
    match C with
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = spfC qFrom q C1 T
                               let E2 = spfC q qTo C2 T
                               merge E1 E2
    | IfStatement(GC)       -> spfGC qFrom qTo GC False T
    | DoStatement(GC)       -> let E1 = spfGC qFrom qFrom GC False T
                               let E2 = Map.add qFrom ((qTo)::(getEdges qFrom T)) T
                               merge E1 E2
    //| _ -> if (qFrom = Start || qTo = End) then Map.add qFrom ((qTo)::(getEdges qFrom T)) T else T
    | _ -> T
and spfGC (qFrom : Node) (qTo : Node) (GC : gcommand) (b : bexpr) (T : SPF) : SPF =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               spfC q qTo C T
    | GCommands(gc1, gc2)   -> match determinism with
                                | false ->  let E1 = spfGC qFrom qTo gc1 b T
                                            let E2 = spfGC qFrom qTo gc2 b T
                                            merge E1 E2
                                | _     ->  match (gc1, gc2) with
                                            | (BooleanGuard(b1, c1), GCommands(gc2gc1, gc2gc3)) ->  let E1 = spfGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    let E2 = spfGC qFrom qTo (GCommands(gc2gc1, gc2gc3)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    merge E1 E2
                                            | (GCommands(gc1, gc2), BooleanGuard(b1, c1))       ->  let E1 = spfGC qFrom qTo (GCommands(gc1, gc2)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    let E2 = spfGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    merge E1 E2
                                            | (BooleanGuard(b1, c1), BooleanGuard(b2, c2)) ->       let E1 = spfGC qFrom qTo (BooleanGuard(And(b1, Neg(b)), c1)) b T
                                                                                                    let E2 = spfGC qFrom qTo (BooleanGuard(And(b2, Neg(And(ParBExpr(b1), Neg(b)))), c2)) (And(b, Neg(ParBExpr(b1)))) T
                                                                                                    merge E1 E2
                                            | _ ->  let E1 = spfGC qFrom qTo gc1 b T
                                                    let E2 = spfGC qFrom qTo gc2 b T
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

let getProgramGraphString (program:Program) = Map.fold (fun state n edgeList -> state + string n + " -> " + (List.fold (fun state (_, _, toNode) -> (if state = "" then state else state + ", ") + string toNode) "" edgeList) + "\n") "" program

let getMemoryString ((varData, arrData):RuntimeData) =
    let varStr varData = Map.fold (fun acc name value -> acc + name + ": " + value.ToString() + "\n") "" varData
    let arrStr arrData = Map.fold (fun acc name arr -> acc + name + ": { " + (List.fold (fun acc v -> acc + (if acc <> "" then ", " + v.ToString() else v.ToString())) "" (List.ofArray arr)) + " }\n") "" arrData
    (varStr varData) + (arrStr arrData)

let rec getViableEdge (edges : Edge list) (memory : RuntimeData) : Option<Edge> =
    match edges with
    | (action, viability, toNode)::xs -> if beval (viability memory) memory then (Some (action, viability, toNode)) else (getViableEdge xs memory)
    | [] -> None

let rec interpret ((current, memory, program):ProgramState) : ProgramState =
    match current with
    | End -> (current, memory, program)
    | _ ->  if debug then printf "%s\n" (current.ToString())
            let edges = Map.find current program
            match (getViableEdge edges memory) with
            | Some (action, viability, toNode) -> (interpret (toNode, (action memory), program))
            | None -> (current, memory, program)

//let rec getStartVariables (current:RuntimeData) : RuntimeData =
//    printf "Please enter one variable at a time. Finish by typing \"quit\"\n"
//    let input = Console.ReadLine()
//    if input = "quit" then current else (parseInput current input)
//and parseInput current input : RuntimeData =
//    if ((input.Contains "[") && (input.Contains "]"))
//    then (parseArray current input)
//    else (parseVariable current input)
//and parseArray (varData, arrData) input : RuntimeData =
//    let inputNoStartBracket = input.Replace("[", "")
//    let inputNoEndBracket = inputNoStartBracket.Replace("]", "")
//    let inputNoWhitespace = inputNoEndBracket.Replace(" ", "")
//    let [|initVar; initVal|] = inputNoWhitespace.Split '='
//    let nums = Array.toList (initVal.Split ',')
//    match nums with
//    |[]     -> failwith "invalid array value"
//    |x      -> getStartVariables ((varData), (arrData.Add (initVar, List.toArray (List.map (fun e -> int e) x))))
//and parseVariable (varData, arrData) input : RuntimeData =
//    let operands = input.Split [|'='|]
//    if operands.Length = 2
//    then getStartVariables ((Map.add ((operands.[0]).Replace (" ", "")) (Int32.Parse ((operands.[1]).Replace (" ", ""))) varData), arrData)
//    else failwith "Couldn't parse variable because there are not 2 operands"

let printProgramState ((node, memory, _) : ProgramState) : string =
    "status: " + (if node = End then "terminated" else "stuck") + "\n" +
    "Node: " + node.ToString() + "\n" +
    getMemoryString memory

let getSPFString (spf:SPF) = Map.fold (fun acc key value -> acc + key.ToString() + " -> " + (List.fold (fun acc value -> acc + value.ToString() + ", ") "" value) + "\n") "" spf
let getDomString (dom:Domain) = Set.fold (fun acc value -> acc + value.ToString() + ", ") "" dom

//let doInterpret =
//    printf "Enter an input program: "
//    let c = parse (Console.ReadLine())
//    let program = edgesC Start End c Map.empty
//    let startVariableData = getStartVariables (Map.empty, Map.empty)
//    let finalData = interpret (Start, startVariableData, program)
//    printf "%s" (printProgramState finalData)

let doProgramValidation =
    printf "Enter an input program: "
    let c = parse (Console.ReadLine())
    let domain = domC Start End c (Set [Start; End])
    //let program = spfC Start End c Map.empty
    printf "%s" (getDomString domain)

// We implement here the function that interacts with the user
let compute =
    doProgramValidation

// Start interacting with the user
compute