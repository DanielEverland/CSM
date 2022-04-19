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
let determinism = false
let debug = true

type Node = | Start
            | End
            | Inter of int
            with override this.ToString() =
                    match this with
                    | Start   -> "qS"
                    | End     -> "qE"
                    | Inter x -> "q" + string x


type Sign = | Plus
            | Minus
            | Zero
            with override this.ToString() =
                    match this with
                    | Plus -> "Plus"
                    | Minus -> "Minus"
                    | Zero -> "Zero"

type NodeSigns = (Map<string, Sign> * Map<string, Set<Sign>>)
type NodeSignsCollection = Set<NodeSigns>
type SignMemory = Map<Node, NodeSignsCollection>

type VariableData = Map<string, int>
type ArrayData = Map<string, int[]>
// The data we can modify during runtime
type RuntimeData = (VariableData * ArrayData)

// Lambdas that take the current runtime data, modify it and return new runtime data
type CompiledAction = RuntimeData -> RuntimeData
type PredicateAction = bexpr -> bexpr
type EdgeViability = RuntimeData -> bexpr
type SignAction = NodeSignsCollection -> NodeSignsCollection

// An edge consists of an action and target node
type Edge = SignAction * PredicateAction * CompiledAction * string * EdgeViability * Node

// A lookup table that determines the edges of all nodes
type Program = Map<Node, Edge list>

type ProgramState = (Node * RuntimeData * Program)

type Domain = Set<Node>
type SubDomain = Set<Node>
type SPFEdge = Node * SubDomain
type SPF = Map<Node, SPFEdge list>
type Predicates = Map<Node, bexpr>

type IterAction = (Node * Node * SPF) -> SPF

let getEdges qFrom T =
    match Map.tryFind qFrom T with
    | Some e -> e
    | None -> []

let merge mapA mapB = Map.fold (fun acc key value -> let edges = getEdges key acc
                                                     Map.add key (value@edges) acc) mapA mapB

let ToString (sd:SubDomain) = Set.fold (fun acc v -> if acc = "" then v.ToString() else acc + ", " + v.ToString()) "" sd

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

let getCartesian a b = 
    Set.fold (fun acc aVal -> (Set.fold (fun accIn bVal -> (Set.add (aVal, bVal) accIn) ) acc b) ) Set.empty a

let getSignSet a b lookup =
    let cartesianProduct = getCartesian a b
    Set.fold (fun acc (x, y) -> Set.union (Map.find y (Map.find x lookup)) acc) Set.empty cartesianProduct

let getVarSignSet (name:string) (col:NodeSignsCollection) : Set<Sign> =
    Set.fold (fun acc (vars, arrs) ->
        let foundVar = match Map.tryFind name vars with
                       | Some v -> set[v]
                       | None -> Set.empty
        let foundArrs = match Map.tryFind name arrs with
                        | Some v -> v
                        | None -> Set.empty
        Set.union (Set.union acc foundVar) foundArrs) Set.empty col

let setVarSignSetOverCollection (n:string) (s:Sign) (c:NodeSignsCollection) : NodeSignsCollection =
    Set.fold (fun acc (vars, arrs) -> Set.add (Map.add n s vars, arrs) acc ) Set.empty c
let setVarSignSet (n:string) (signs:Set<Sign>) (c:NodeSignsCollection) : NodeSignsCollection = 
    Set.fold (fun acc s -> Set.union acc (setVarSignSetOverCollection n s c)) Set.empty signs

let flipSigns (s:Set<Sign>) = Set.fold (fun acc v -> Set.add (if v = Plus then Minus else if v = Minus then Plus else Zero) acc) Set.empty s
    
let plusSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [Minus]);               (Zero, set [Minus]);    (Plus, set [Minus; Zero; Plus]) ])
    (Zero,      Map.ofList [    (Minus, set [Minus]);               (Zero, set [Zero]);     (Plus, set [Plus]) ])
    (Plus,      Map.ofList [    (Minus, set [Minus; Zero; Plus]);   (Zero, set [Plus]);     (Plus, set [Plus]) ]) ]

let minusSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [Minus; Zero; Plus]);   (Zero, set [Minus]);    (Plus, set [Minus]) ])
    (Zero,      Map.ofList [    (Minus, set [Plus]);                (Zero, set [Zero]);     (Plus, set [Minus]) ])
    (Plus,      Map.ofList [    (Minus, set [Plus]);                (Zero, set [Plus]);     (Plus, set [Minus; Zero; Plus]) ]) ]

let timesSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [Plus]);    (Zero, set [Zero]);     (Plus, set [Minus]) ])
    (Zero,      Map.ofList [    (Minus, set [Zero]);    (Zero, set [Zero]);     (Plus, set [Zero]) ])
    (Plus,      Map.ofList [    (Minus, set [Minus]);   (Zero, set [Zero]);     (Plus, set [Plus]) ]) ]

let divisionSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [Plus]);    (Zero, set []);     (Plus, set [Minus]) ])
    (Zero,      Map.ofList [    (Minus, set [Zero]);    (Zero, set []);     (Plus, set [Zero]) ])
    (Plus,      Map.ofList [    (Minus, set [Minus]);   (Zero, set []);     (Plus, set [Plus]) ]) ]

let powSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [Minus; Plus]);     (Zero, set [Plus]);     (Plus, set [Minus; Plus]) ])
    (Zero,      Map.ofList [    (Minus, set []);                (Zero, set [Plus]);     (Plus, set [Zero]) ])
    (Plus,      Map.ofList [    (Minus, set [Plus]);            (Zero, set [Plus]);     (Plus, set [Plus]) ]) ]

let equalSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [False]);    (Plus, set [False]) ])
    (Zero,      Map.ofList [    (Minus, set [False]);       (Zero, set [True]);     (Plus, set [False]) ])
    (Plus,      Map.ofList [    (Minus, set [False]);       (Zero, set [False]);    (Plus, set [True; False]) ]) ]

let notEqualSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [True]);     (Plus, set [True]) ])
    (Zero,      Map.ofList [    (Minus, set [True]);        (Zero, set [False]);    (Plus, set [True]) ])
    (Plus,      Map.ofList [    (Minus, set [True]);        (Zero, set [True]);     (Plus, set [True; False]) ]) ]

let greaterSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [False]);    (Plus, set [False]) ])
    (Zero,      Map.ofList [    (Minus, set [True]);        (Zero, set [False]);    (Plus, set [False]) ])
    (Plus,      Map.ofList [    (Minus, set [True]);        (Zero, set [True]);     (Plus, set [True; False]) ]) ]

let greaterEqualSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [False]);    (Plus, set [False]) ])
    (Zero,      Map.ofList [    (Minus, set [True]);        (Zero, set [True]);     (Plus, set [False]) ])
    (Plus,      Map.ofList [    (Minus, set [True]);        (Zero, set [True]);     (Plus, set [True; False]) ]) ]

let lessSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [True]);     (Plus, set [True]) ])
    (Zero,      Map.ofList [    (Minus, set [False]);       (Zero, set [False]);    (Plus, set [True]) ])
    (Plus,      Map.ofList [    (Minus, set [False]);       (Zero, set [False]);    (Plus, set [True; False]) ]) ]

let lessEqualSignLookup =  Map.ofList [ 
    (Minus,     Map.ofList [    (Minus, set [True; False]); (Zero, set [True]);     (Plus, set [True]) ])
    (Zero,      Map.ofList [    (Minus, set [False]);       (Zero, set [True]);     (Plus, set [True]) ])
    (Plus,      Map.ofList [    (Minus, set [False]);       (Zero, set [False]);    (Plus, set [True; False]) ]) ]

let andSignLookup =  Map.ofList [
    (True,  Map.ofList [    (True, set [True]);     (False, set [False]) ])
    (False, Map.ofList [    (True, set [False]);    (False, set [False]) ]) ]

let orSignLookup =  Map.ofList [
    (True,  Map.ofList [    (True, set [True]);     (False, set [True]) ])
    (False, Map.ofList [    (True, set [True]);     (False, set [False]) ]) ]

let rec aevalSign expr (signs : NodeSignsCollection) : Set<Sign> = 
    match expr with
    | Num x             -> if x > 0 then set [Plus] else if x < 0 then set [Minus] else set [Zero]
    | Var n             -> getVarSignSet n signs
    | Array(n, i)       -> if (Set.intersect (aevalSign i signs) (set[Zero; Plus])).IsEmpty then Set.empty else (getVarSignSet n signs)
    | TimesExpr(x,y)    -> getSignSet (aevalSign x signs) (aevalSign y signs) timesSignLookup
    | DivExpr(x,y)      -> getSignSet (aevalSign x signs) (aevalSign y signs) divisionSignLookup
    | PlusExpr(x, y)    -> getSignSet (aevalSign x signs) (aevalSign y signs) plusSignLookup
    | MinusExpr(x, y)   -> getSignSet (aevalSign x signs) (aevalSign y signs) minusSignLookup
    | PowExpr(x,y)      -> getSignSet (aevalSign x signs) (aevalSign y signs) powSignLookup
    | UPlusExpr(x)      -> aevalSign x signs
    | UMinusExpr(x)     -> flipSigns (aevalSign x signs)
    | ParAExpr(x)       -> aevalSign x signs
and bevalsign e (signs : NodeSignsCollection) : Set<bexpr> =
  match e with
    | True                  -> set [True]
    | False                 -> set [False]
    | And(x, y)             -> let lhs = bevalsign x signs
                               let rhs = bevalsign y signs
                               getSignSet lhs rhs andSignLookup
    | Or(x, y)              -> let lhs = bevalsign x signs
                               let rhs = bevalsign y signs
                               getSignSet lhs rhs orSignLookup
    | SAnd(x, y)            -> let lhs = bevalsign x signs
                               let rhs = bevalsign y signs
                               getSignSet lhs rhs andSignLookup
    | SOr(x, y)             -> let lhs = bevalsign x signs
                               let rhs = bevalsign y signs
                               getSignSet lhs rhs orSignLookup
    | Neg(x)                -> Set.fold (fun acc v -> Set.add (Neg(v)) acc) Set.empty (bevalsign x signs)
    | Equal(x, y)           -> getSignSet (aevalSign x signs) (aevalSign y signs) equalSignLookup
    | NEqual(x, y)          -> getSignSet (aevalSign x signs) (aevalSign y signs) notEqualSignLookup
    | Greater(x, y)         -> let lhs = (aevalSign x signs)
                               let rhs = (aevalSign y signs)
                               (printfn "%A > %A" lhs rhs)
                               getSignSet (aevalSign x signs) (aevalSign y signs) greaterSignLookup
    | GreaterEqual(x, y)    -> getSignSet (aevalSign x signs) (aevalSign y signs) greaterEqualSignLookup
    | Less(x, y)            -> getSignSet (aevalSign x signs) (aevalSign y signs) lessSignLookup
    | LessEqual(x, y)       -> getSignSet (aevalSign x signs) (aevalSign y signs) lessEqualSignLookup
    | ParBExpr(x)           -> bevalsign x signs

let rec replaceInPredicateB varName expr p : bexpr =
    match p with
    | True -> True
    | False -> False
    | And(a, b) -> And( (replaceInPredicateB varName expr a), (replaceInPredicateB varName expr b) )
    | Or(a, b) -> Or( (replaceInPredicateB varName expr a), (replaceInPredicateB varName expr b) )
    | SAnd(a, b) -> SAnd( (replaceInPredicateB varName expr a), (replaceInPredicateB varName expr b) )
    | SOr(a, b) -> SOr( (replaceInPredicateB varName expr a), (replaceInPredicateB varName expr b) )
    | Neg(a) -> Neg(replaceInPredicateB varName expr a)
    | Equal(a, b) -> Equal( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | NEqual(a, b) -> NEqual( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | Greater(a, b) -> Greater( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | GreaterEqual(a, b) -> GreaterEqual( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | Less(a, b) -> Less( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | LessEqual(a, b) -> LessEqual( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | ParBExpr(a) -> ParBExpr(replaceInPredicateB varName expr a)
and replaceInPredicateA varName expr (p:aexpr) : aexpr =
    match p with
    | Num(a) -> Num(a)
    | Var(a) -> if a = varName then ParAExpr(expr) else Var(a)
    | Array(a, b) -> Array(a, b)
    | TimesExpr(a, b) -> TimesExpr( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | DivExpr(a, b) -> DivExpr( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | PlusExpr(a, b) -> PlusExpr( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | MinusExpr(a, b) -> MinusExpr( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | PowExpr(a, b) -> PowExpr( (replaceInPredicateA varName expr a), (replaceInPredicateA varName expr b) )
    | UPlusExpr(a) -> UPlusExpr( (replaceInPredicateA varName expr a) )
    | UMinusExpr(a) -> UMinusExpr( (replaceInPredicateA varName expr a) )
    | ParAExpr(a) -> ParAExpr( (replaceInPredicateA varName expr a) )

let rec peval (p:bexpr) (c:command) : bexpr =
    match c with
    | AssignExpr(varName, expr) -> replaceInPredicateB varName expr p
    | Commands(a, b) -> peval (peval p b) a
    | DoStatement(GC) -> gcpeval p GC
    | IfStatement(GC) -> gcpeval p GC
    | _ -> failwith ("I don't know what to do with " + c.GetType().ToString())
and gcpeval (p:bexpr) (gc:gcommand) : bexpr =
    match gc with
    | BooleanGuard(b, C) -> peval p C
    | GCommands(a, b) -> gcpeval (gcpeval p b) a

let printEdge qFrom label qTo = qFrom.ToString() + " -> " + qTo.ToString() + " [label = \"" + label + "\"];"

let mutable n = 0
let getFresh q = match q with
                 | Start|Inter _ -> n <- n + 1
                                    Inter n
                 | End           -> failwith "qFrom can't be end node"

let rec doneGC = function
    | BooleanGuard(x,_)     -> Neg(ParBExpr(x))
    | GCommands(x,y)        -> Or((doneGC x), (doneGC y))

let rec edgesC (qFrom : Node) (qTo : Node) (C : command) (T : Program) : Program =
    match C with
    | AssignExpr(x,y)       -> Map.add qFrom (((fun M -> setVarSignSet x (aevalSign y M) M), (fun expr -> peval expr C), (fun runtimeData -> ceval (AssignExpr(x, y)) runtimeData), C.ToString(), (fun runtimeData -> True), qTo)::(getEdges qFrom T)) T
    | AssignArray(x,y,z)    -> Map.add qFrom (((fun a -> a), (fun expr -> peval expr C), (fun runtimeData -> ceval (AssignArray(x, y, z)) runtimeData), C.ToString(), (fun runtimeData -> True), qTo)::(getEdges qFrom T)) T
    | Skip                  -> T
    | Commands(C1,C2)       -> let q = getFresh qFrom
                               let E1 = edgesC qFrom q C1 T
                               let E2 = edgesC q qTo C2 T
                               merge E1 E2
    | IfStatement(GC)       -> edgesGC qFrom qTo GC False T
    | DoStatement(GC)       -> let E1 = edgesGC qFrom qFrom GC False T
                               let E2 = Map.add qFrom (((fun a -> a), (fun expr -> expr), (fun runtimeData -> ceval (DoStatement(GC)) runtimeData), (doneGC GC).ToString(), (fun runtimeData -> doneGC GC), qTo)::(getEdges qFrom T)) T
                               merge E1 E2
and edgesGC (qFrom : Node) (qTo : Node) (GC : gcommand) (b : bexpr) (T : Program) : Program =
    match GC with
    | BooleanGuard(b, C)    -> let q = getFresh qFrom
                               let E = edgesC q qTo C T
                               Map.add qFrom (((fun a -> (printfn "%A" (bevalsign b a))
                                                         if Set.contains True (bevalsign b a) then a else Set.empty), (fun expr -> expr), (fun runtimeData -> runtimeData), b.ToString(), (fun runtimeData -> b), q)::(getEdges qFrom T)) E
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

let getActionStr (qFrom:Node) (qTo:Node) (P:Program) = let (_, _, _, str, _, _) = List.find (fun (_, _, _, _, _, toNode) -> qTo = toNode) (Map.find qFrom P)
                                                       str

//let addIfDom (qFrom:Node) (qTo : Node) (dom:Domain) (T:SPF) : SPF = if dom.Contains qFrom then Map.add qFrom ((qTo, [])::(getEdges qFrom T)) T else T

let getAllEdges (P:Program) : Edge list = Map.fold (fun acc key value -> acc@value) [] P
let filterByEnd (N:Node) (E:(Edge list)) : Edge list = List.filter (fun (_, _, _, _, _, endNode) -> endNode = N) E
let getValidEdges (N:Node) (P:Program) : Program = Map.fold (fun acc key edges ->   let filteredEdges = filterByEnd N edges
                                                                                    if List.isEmpty filteredEdges
                                                                                    then acc
                                                                                    else Map.add key (filterByEnd N edges) acc) Map.empty P
let iterateOverEdges (iter:IterAction) (P:Program) (S:SPF) = Map.fold (fun mapAcc qFrom edges -> (List.fold (fun listAcc (_, _, _, _, _, qTo) -> (iter (qFrom, qTo, listAcc)) )) mapAcc edges) S P
let unionS (a:SPF) (b:SPF) : SPF = Map.fold (fun acc key (value:SPFEdge list) -> let edges = List.filter (fun (v:SPFEdge) -> (List.contains v value) = false) (getEdges key acc)
                                                                                 Map.add key (value@edges) acc) a b

let addToSubDomain (qFrom:Node) (qTo : Node) (D:SubDomain) : SubDomain = Set.union (set [qFrom; qTo]) D

let rec build (qFrom:Node) (qTo : Node) (D:Domain) (P:Program) (S:SPF) (SD:SubDomain) : SPF =
    let validEdges = getValidEdges qFrom P
    iterateOverEdges (fun (q, _, newS) -> if D.Contains q
                                             then unionS newS (Map.ofList [(q, [qTo, (addToSubDomain q qTo SD)])])
                                             else unionS newS (build q qTo D P newS (addToSubDomain q qTo SD))
                                             ) validEdges S

//let getPredicateFromUser (node:Node) : string =
//    printf "%s" ("Enter predicate for " + node.ToString() + ": ")
//    Console.ReadLine()
//let rec buildPredicates (D:Node list) (P:Predicates) : Predicates =
//    match D with
//    | x::xs -> buildPredicates xs (Map.add x (getPredicateFromUser x) P)
//    | _ -> P

let getNextEdge (q:Node) (P:Program) (D:SubDomain) : Option<Node> =
    let allEdges = Map.find q P
    match (List.tryFind (fun (_, _, _, _, _, e) -> Set.contains e D) allEdges) with
    | Some (_, _, _, _, _, e) -> Some e
    | None -> None    
let buildSPFEdgePath (qS:Node) (qE:Node, D:SubDomain) (P:Program) : Node list =
    let rec dfs (curr:Node) (l:Node list) : Node list =
        match getNextEdge curr P D with
        | Some next -> if next = qE then l@[curr; next] else dfs next (l@[curr])
        | None -> failwith "dfs failed"
    dfs qS []
    
let getSubPathString (qFrom:Node) (edge:SPFEdge) (P:Program) : string =
    let path = buildSPFEdgePath qFrom edge P
    let rec buildStr acc = function
    | qStart::qEnd::qs -> let edgeStr = if debug then "[ (" + qStart.ToString() + "->" + qEnd.ToString() + ") = " + getActionStr qStart qEnd P + " ]" else getActionStr qStart qEnd P
                          if acc = "" then (buildStr edgeStr (qEnd::qs)) else buildStr (acc + ", " + edgeStr) (qEnd::qs)
    | _ -> acc
    buildStr "" path

let rec buildProofObligationsKeyValuePair (from:Node) (edges:SPFEdge list) (P:Predicates) (pro:Program) : string =
    List.fold (fun acc edge -> acc + "\n" + (buildProofObligationsWithEdge from edge P pro)) "" edges
and buildProofObligationsWithEdge (from:Node) (qTo, sd) (P:Predicates) (pro:Program) : string = 
    (Map.find from P).ToString() + " " + (getSubPathString from (qTo, sd) pro)  + " " + (Map.find qTo P).ToString()
let buildProofObligations (S:SPF) (P:Predicates) (pro:Program) : string =
    Map.fold (fun acc key edgeList -> acc + (buildProofObligationsKeyValuePair key edgeList P pro)) "" S

let transformPredicate (qFrom:Node) (edge:SPFEdge) (P:Program) (bStart:bexpr) : bexpr =
    let path = List.rev (buildSPFEdgePath qFrom edge P)
    let rec doTransform b = function
    | qStart::qEnd::qs -> let (_, act, _, str, _, _) = List.find (fun (_, _, _, _, _, toNode) -> qStart = toNode) (Map.find qEnd P)
                          doTransform (act b) (qEnd::qs)
    | _ -> b
    doTransform bStart path

let rec buildContractKeyValuePair (from:Node) (edges:SPFEdge list) (P:Predicates) (pro:Program) : string =
    List.fold (fun acc edge -> acc + "\n" + (buildContractWithEdge from edge P pro)) "" edges
and buildContractWithEdge (from:Node) (qTo, sd) (P:Predicates) (pro:Program) : string = 
    (Map.find from P).ToString() + " => " + (transformPredicate from (qTo, sd) pro (Map.find qTo P)).ToString()
let buildContract (S:SPF) (P:Predicates) (pro:Program) : string =
    Map.fold (fun acc key edgeList -> acc + (buildContractKeyValuePair key edgeList P pro)) "" S

//let isSubset (a:NodeSigns list) (b:NodeSigns list) : bool =
//    List.fold (fun acc v -> if acc = false then (List.contains v b) else acc) false a

let createInitialMemory (P:Program) (A:SignMemory) : SignMemory = 
    Map.fold (fun acc key _ -> if key <> Start then (Map.add key Set.empty acc) else acc) (Map.add End Set.empty A) P
let signAnalysis (P:Program) (qInit:Node) (A:SignMemory) : SignMemory = 
    let initializedMemory = createInitialMemory P A
    if debug then printfn "%A" initializedMemory
    let Winit = [Start]
    let rec iterWorklist A W : SignMemory =
        match W with
        | q::qs -> let (newMemory, newWorklist) = doForAllEdges q qs A (getEdges q P)
                   iterWorklist newMemory newWorklist
        | _ -> A
    and doForAllEdges q W A edges : (SignMemory * Node list) =
        match edges with
        | (action, _, _, _, _, toNode)::es -> if debug then printfn "\n%s -> %A\n" (q.ToString()) A
                                              let newSigns = action (Map.find q A)
                                              let endSigns = Map.find toNode A
                                              if Set.isSubset newSigns endSigns
                                              then doForAllEdges q W A es
                                              else doForAllEdges q (toNode::W) (Map.add toNode (Set.union newSigns endSigns) A) es
        | _ -> (A, W)
    iterWorklist initializedMemory Winit

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

let getProgramGraphString (program:Program) = Map.fold (fun state n edgeList -> state + string n + " -> " + (List.fold (fun state (_, _, _, _, _, toNode) -> (if state = "" then state else state + ", ") + string toNode) "" edgeList) + "\n") "" program

let getMemoryString ((varData, arrData):RuntimeData) =
    let varStr varData = Map.fold (fun acc name value -> acc + name + ": " + value.ToString() + "\n") "" varData
    let arrStr arrData = Map.fold (fun acc name arr -> acc + name + ": { " + (List.fold (fun acc v -> acc + (if acc <> "" then ", " + v.ToString() else v.ToString())) "" (List.ofArray arr)) + " }\n") "" arrData
    (varStr varData) + (arrStr arrData)

let rec getViableEdge (edges : Edge list) (memory : RuntimeData) : Option<Edge> =
    match edges with
    | (sAction, pAction, action, actionName, viability, toNode)::xs -> if beval (viability memory) memory then (Some (sAction, pAction, action, actionName, viability, toNode)) else (getViableEdge xs memory)
    | [] -> None

let rec interpret ((current, memory, program):ProgramState) : ProgramState =
    match current with
    | End -> (current, memory, program)
    | _ ->  if debug then printf "%s\n" (current.ToString())
            let edges = Map.find current program
            match (getViableEdge edges memory) with
            | Some (_, _, action, _, _, toNode) -> (interpret (toNode, (action memory), program))
            | None -> (current, memory, program)

let parseSign input = 
    match input with
    | "+" -> Plus
    | "-" -> Minus
    | "0" -> Zero
    | _ -> failwith ("Could not parse " + input)

let rec getStartSigns (current:NodeSigns) : NodeSigns =
    printf "Please enter one variable at a time. Finish by typing \"quit\"\n"
    let input = Console.ReadLine()
    if input = "quit" then current else (parseSignInput current input)
and parseSignInput current input : NodeSigns =
    if ((input.Contains "{") && (input.Contains "}"))
    then (parseSignArray current input)
    else (parseSignVariable current input)
and parseSignArray (varData, arrData) input : NodeSigns =
    let inputNoStartBracket = input.Replace("{", "")
    let inputNoEndBracket = inputNoStartBracket.Replace("}", "")
    let inputNoWhitespace = inputNoEndBracket.Replace(" ", "")
    let [|initVar; initVal|] = inputNoWhitespace.Split '='
    let nums = Array.toList (initVal.Split ',')
    match nums with
    |[]     -> failwith "invalid array value"
    |x      -> getStartSigns (varData, ( arrData.Add (initVar, set (List.map (fun e -> parseSign e) x)) ))
and parseSignVariable (varData, arrData) input : NodeSigns =
    let operands = input.Split [|'='|]
    if operands.Length = 2
    then getStartSigns ((Map.add ((operands.[0]).Replace (" ", "")) (parseSign ((operands.[1]).Replace (" ", ""))) varData), arrData)
    else failwith "Couldn't parse variable because there are not 2 operands"

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

//let doProgramValidation =
//    // Example 1
//    let c = parse "q:=0; do m>=n -> m:=m-n; q:=q+1 od"
//    let predicates = Map.ofList [
//        ( Start, Equal(Var("M"), Var("m")) );
//        ( Inter(1), Equal(Var("M"), PlusExpr( TimesExpr(Var("q"), Var("n")), Var("m")) ) );
//        ( End, Equal(Var("M"), PlusExpr( TimesExpr(Var("q"), Var("n")), Var("m") ) ) )
//    ]

//    // Example 2
//    //let c = parse "x:=2*y; y:=7; x:=x*y"
//    //let predicates = Map.ofList [
//    //    ( Start, Greater( TimesExpr( TimesExpr(Num(2), Var("y")), Num(7) ), Num(42) ) );
//    //    ( End, Greater(Var("x"), Num(42)) )
//    //]

//    let domain = domC Start End c (Set [Start; End])

//    // Reset "get fresh" function
//    n <- 0
//    let program = edgesC Start End c Map.empty
//    let spf = Set.fold (fun acc q -> unionS acc (build q q domain program acc Set.empty) ) Map.empty domain
//    printfn "%s" (buildContract spf predicates program)

let doSignAnalysis =
    let c = parse "do x>0 -> x:=x-1 od"
    let firstSigns = (Map.ofList [("x", Plus)], Map.empty)

    //let c = parse "y:=1; do x>0 -> y:=x*y; x:=x-1 od"
    //let firstSigns = (Map.ofList [("x", Plus); ("y", Plus)], Map.empty)

    //let c = parse "y:=2; z:=y*-1"
    //let firstSigns = (Map.ofList [("y", Plus); ("z", Plus)], Map.empty)
    //let firstSigns = getStartSigns (Map.empty, Map.empty)
    let program = edgesC Start End c Map.empty    
    let signMemory = Map.ofList [(Start, (set [firstSigns]))]
    printfn "%A" (signAnalysis program Start signMemory)                              

// Start interacting with the user
doSignAnalysis