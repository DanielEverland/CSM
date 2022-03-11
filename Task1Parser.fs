// Implementation file for parser generated by fsyacc
module Task1Parser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 2 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"

open Task1TypesAST

# 10 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | AND
  | OR
  | SAND
  | SOR
  | NEG
  | EQUAL
  | NEQUAL
  | GT
  | GEQ
  | LT
  | LEQ
  | TRUE
  | FALSE
  | TIMES
  | DIV
  | PLUS
  | MINUS
  | POW
  | LPAR
  | RPAR
  | EOF
  | VARIABLE
  | ASSIGN
  | SEMICOLON
  | IFSTART
  | IFEND
  | DOSTART
  | DOEND
  | ARROW
  | DOUBLEBRACKETS
  | NUM of (float)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_AND
    | TOKEN_OR
    | TOKEN_SAND
    | TOKEN_SOR
    | TOKEN_NEG
    | TOKEN_EQUAL
    | TOKEN_NEQUAL
    | TOKEN_GT
    | TOKEN_GEQ
    | TOKEN_LT
    | TOKEN_LEQ
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_TIMES
    | TOKEN_DIV
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_POW
    | TOKEN_LPAR
    | TOKEN_RPAR
    | TOKEN_EOF
    | TOKEN_VARIABLE
    | TOKEN_ASSIGN
    | TOKEN_SEMICOLON
    | TOKEN_IFSTART
    | TOKEN_IFEND
    | TOKEN_DOSTART
    | TOKEN_DOEND
    | TOKEN_ARROW
    | TOKEN_DOUBLEBRACKETS
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_gc
    | NONTERM_command
    | NONTERM_bexpression
    | NONTERM_aexpression

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | AND  -> 0 
  | OR  -> 1 
  | SAND  -> 2 
  | SOR  -> 3 
  | NEG  -> 4 
  | EQUAL  -> 5 
  | NEQUAL  -> 6 
  | GT  -> 7 
  | GEQ  -> 8 
  | LT  -> 9 
  | LEQ  -> 10 
  | TRUE  -> 11 
  | FALSE  -> 12 
  | TIMES  -> 13 
  | DIV  -> 14 
  | PLUS  -> 15 
  | MINUS  -> 16 
  | POW  -> 17 
  | LPAR  -> 18 
  | RPAR  -> 19 
  | EOF  -> 20 
  | VARIABLE  -> 21 
  | ASSIGN  -> 22 
  | SEMICOLON  -> 23 
  | IFSTART  -> 24 
  | IFEND  -> 25 
  | DOSTART  -> 26 
  | DOEND  -> 27 
  | ARROW  -> 28 
  | DOUBLEBRACKETS  -> 29 
  | NUM _ -> 30 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_AND 
  | 1 -> TOKEN_OR 
  | 2 -> TOKEN_SAND 
  | 3 -> TOKEN_SOR 
  | 4 -> TOKEN_NEG 
  | 5 -> TOKEN_EQUAL 
  | 6 -> TOKEN_NEQUAL 
  | 7 -> TOKEN_GT 
  | 8 -> TOKEN_GEQ 
  | 9 -> TOKEN_LT 
  | 10 -> TOKEN_LEQ 
  | 11 -> TOKEN_TRUE 
  | 12 -> TOKEN_FALSE 
  | 13 -> TOKEN_TIMES 
  | 14 -> TOKEN_DIV 
  | 15 -> TOKEN_PLUS 
  | 16 -> TOKEN_MINUS 
  | 17 -> TOKEN_POW 
  | 18 -> TOKEN_LPAR 
  | 19 -> TOKEN_RPAR 
  | 20 -> TOKEN_EOF 
  | 21 -> TOKEN_VARIABLE 
  | 22 -> TOKEN_ASSIGN 
  | 23 -> TOKEN_SEMICOLON 
  | 24 -> TOKEN_IFSTART 
  | 25 -> TOKEN_IFEND 
  | 26 -> TOKEN_DOSTART 
  | 27 -> TOKEN_DOEND 
  | 28 -> TOKEN_ARROW 
  | 29 -> TOKEN_DOUBLEBRACKETS 
  | 30 -> TOKEN_NUM 
  | 33 -> TOKEN_end_of_input
  | 31 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startstart 
    | 1 -> NONTERM_start 
    | 2 -> NONTERM_gc 
    | 3 -> NONTERM_gc 
    | 4 -> NONTERM_command 
    | 5 -> NONTERM_command 
    | 6 -> NONTERM_command 
    | 7 -> NONTERM_bexpression 
    | 8 -> NONTERM_bexpression 
    | 9 -> NONTERM_bexpression 
    | 10 -> NONTERM_bexpression 
    | 11 -> NONTERM_bexpression 
    | 12 -> NONTERM_bexpression 
    | 13 -> NONTERM_bexpression 
    | 14 -> NONTERM_bexpression 
    | 15 -> NONTERM_bexpression 
    | 16 -> NONTERM_bexpression 
    | 17 -> NONTERM_bexpression 
    | 18 -> NONTERM_bexpression 
    | 19 -> NONTERM_bexpression 
    | 20 -> NONTERM_bexpression 
    | 21 -> NONTERM_aexpression 
    | 22 -> NONTERM_aexpression 
    | 23 -> NONTERM_aexpression 
    | 24 -> NONTERM_aexpression 
    | 25 -> NONTERM_aexpression 
    | 26 -> NONTERM_aexpression 
    | 27 -> NONTERM_aexpression 
    | 28 -> NONTERM_aexpression 
    | 29 -> NONTERM_aexpression 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 33 
let _fsyacc_tagOfErrorTerminal = 31

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | AND  -> "AND" 
  | OR  -> "OR" 
  | SAND  -> "SAND" 
  | SOR  -> "SOR" 
  | NEG  -> "NEG" 
  | EQUAL  -> "EQUAL" 
  | NEQUAL  -> "NEQUAL" 
  | GT  -> "GT" 
  | GEQ  -> "GEQ" 
  | LT  -> "LT" 
  | LEQ  -> "LEQ" 
  | TRUE  -> "TRUE" 
  | FALSE  -> "FALSE" 
  | TIMES  -> "TIMES" 
  | DIV  -> "DIV" 
  | PLUS  -> "PLUS" 
  | MINUS  -> "MINUS" 
  | POW  -> "POW" 
  | LPAR  -> "LPAR" 
  | RPAR  -> "RPAR" 
  | EOF  -> "EOF" 
  | VARIABLE  -> "VARIABLE" 
  | ASSIGN  -> "ASSIGN" 
  | SEMICOLON  -> "SEMICOLON" 
  | IFSTART  -> "IFSTART" 
  | IFEND  -> "IFEND" 
  | DOSTART  -> "DOSTART" 
  | DOEND  -> "DOEND" 
  | ARROW  -> "ARROW" 
  | DOUBLEBRACKETS  -> "DOUBLEBRACKETS" 
  | NUM _ -> "NUM" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | AND  -> (null : System.Object) 
  | OR  -> (null : System.Object) 
  | SAND  -> (null : System.Object) 
  | SOR  -> (null : System.Object) 
  | NEG  -> (null : System.Object) 
  | EQUAL  -> (null : System.Object) 
  | NEQUAL  -> (null : System.Object) 
  | GT  -> (null : System.Object) 
  | GEQ  -> (null : System.Object) 
  | LT  -> (null : System.Object) 
  | LEQ  -> (null : System.Object) 
  | TRUE  -> (null : System.Object) 
  | FALSE  -> (null : System.Object) 
  | TIMES  -> (null : System.Object) 
  | DIV  -> (null : System.Object) 
  | PLUS  -> (null : System.Object) 
  | MINUS  -> (null : System.Object) 
  | POW  -> (null : System.Object) 
  | LPAR  -> (null : System.Object) 
  | RPAR  -> (null : System.Object) 
  | EOF  -> (null : System.Object) 
  | VARIABLE  -> (null : System.Object) 
  | ASSIGN  -> (null : System.Object) 
  | SEMICOLON  -> (null : System.Object) 
  | IFSTART  -> (null : System.Object) 
  | IFEND  -> (null : System.Object) 
  | DOSTART  -> (null : System.Object) 
  | DOEND  -> (null : System.Object) 
  | ARROW  -> (null : System.Object) 
  | DOUBLEBRACKETS  -> (null : System.Object) 
  | NUM _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us; 65535us; 1us; 65535us; 0us; 1us; 3us; 65535us; 10us; 7us; 13us; 8us; 15us; 9us; 3us; 65535us; 0us; 2us; 5us; 6us; 12us; 11us; 9us; 65535us; 10us; 4us; 13us; 4us; 15us; 4us; 25us; 19us; 26us; 20us; 27us; 21us; 28us; 22us; 29us; 23us; 44us; 24us; 23us; 65535us; 10us; 30us; 13us; 30us; 15us; 30us; 25us; 30us; 26us; 30us; 27us; 30us; 28us; 30us; 29us; 30us; 32us; 33us; 34us; 35us; 36us; 37us; 38us; 39us; 40us; 41us; 42us; 43us; 44us; 31us; 54us; 46us; 55us; 47us; 56us; 48us; 57us; 49us; 58us; 50us; 59us; 51us; 60us; 52us; 61us; 53us; |]
let _fsyacc_sparseGotoTableRowOffsets = [|0us; 1us; 3us; 7us; 11us; 21us; |]
let _fsyacc_stateToProdIdxsTableElements = [| 1us; 0us; 1us; 0us; 2us; 1us; 4us; 1us; 1us; 5us; 2us; 9us; 10us; 11us; 12us; 1us; 2us; 2us; 2us; 4us; 2us; 3us; 3us; 2us; 3us; 5us; 2us; 3us; 6us; 1us; 3us; 2us; 4us; 4us; 1us; 4us; 1us; 5us; 1us; 5us; 1us; 6us; 1us; 6us; 1us; 7us; 1us; 8us; 5us; 9us; 9us; 10us; 11us; 12us; 5us; 9us; 10us; 10us; 11us; 12us; 5us; 9us; 10us; 11us; 11us; 12us; 5us; 9us; 10us; 11us; 12us; 12us; 5us; 9us; 10us; 11us; 12us; 13us; 5us; 9us; 10us; 11us; 12us; 20us; 1us; 9us; 1us; 10us; 1us; 11us; 1us; 12us; 1us; 13us; 11us; 14us; 15us; 16us; 17us; 18us; 19us; 21us; 22us; 23us; 24us; 25us; 12us; 14us; 15us; 16us; 17us; 18us; 19us; 21us; 22us; 23us; 24us; 25us; 28us; 1us; 14us; 6us; 14us; 21us; 22us; 23us; 24us; 25us; 1us; 15us; 6us; 15us; 21us; 22us; 23us; 24us; 25us; 1us; 16us; 6us; 16us; 21us; 22us; 23us; 24us; 25us; 1us; 17us; 6us; 17us; 21us; 22us; 23us; 24us; 25us; 1us; 18us; 6us; 18us; 21us; 22us; 23us; 24us; 25us; 1us; 19us; 6us; 19us; 21us; 22us; 23us; 24us; 25us; 2us; 20us; 28us; 1us; 20us; 6us; 21us; 21us; 22us; 23us; 24us; 25us; 6us; 21us; 22us; 22us; 23us; 24us; 25us; 6us; 21us; 22us; 23us; 23us; 24us; 25us; 6us; 21us; 22us; 23us; 24us; 24us; 25us; 6us; 21us; 22us; 23us; 24us; 25us; 25us; 6us; 21us; 22us; 23us; 24us; 25us; 26us; 6us; 21us; 22us; 23us; 24us; 25us; 27us; 6us; 21us; 22us; 23us; 24us; 25us; 28us; 1us; 21us; 1us; 22us; 1us; 23us; 1us; 24us; 1us; 25us; 1us; 26us; 1us; 27us; 1us; 28us; 1us; 28us; 1us; 29us; |]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us; 2us; 4us; 7us; 9us; 15us; 17us; 20us; 23us; 26us; 29us; 31us; 34us; 36us; 38us; 40us; 42us; 44us; 46us; 48us; 54us; 60us; 66us; 72us; 78us; 84us; 86us; 88us; 90us; 92us; 94us; 106us; 119us; 121us; 128us; 130us; 137us; 139us; 146us; 148us; 155us; 157us; 164us; 166us; 173us; 176us; 178us; 185us; 192us; 199us; 206us; 213us; 220us; 227us; 234us; 236us; 238us; 240us; 242us; 244us; 246us; 248us; 250us; 252us; |]
let _fsyacc_action_rows = 64
let _fsyacc_actionTableElements = [|2us; 32768us; 24us; 13us; 26us; 15us; 0us; 49152us; 2us; 32768us; 20us; 3us; 23us; 12us; 0us; 16385us; 5us; 32768us; 0us; 25us; 1us; 26us; 2us; 27us; 3us; 28us; 28us; 5us; 2us; 32768us; 24us; 13us; 26us; 15us; 1us; 16386us; 23us; 12us; 0us; 16387us; 2us; 32768us; 25us; 14us; 29us; 10us; 2us; 32768us; 27us; 16us; 29us; 10us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 0us; 16388us; 2us; 32768us; 24us; 13us; 26us; 15us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 0us; 16389us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 0us; 16390us; 0us; 16391us; 0us; 16392us; 0us; 16393us; 0us; 16394us; 0us; 16395us; 0us; 16396us; 0us; 16397us; 5us; 32768us; 0us; 25us; 1us; 26us; 2us; 27us; 3us; 28us; 19us; 45us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 11us; 32768us; 5us; 32us; 6us; 34us; 7us; 36us; 8us; 38us; 9us; 40us; 10us; 42us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 12us; 32768us; 5us; 32us; 6us; 34us; 7us; 36us; 8us; 38us; 9us; 40us; 10us; 42us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 19us; 62us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16398us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16399us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16400us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16401us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16402us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 5us; 16403us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 7us; 32768us; 4us; 29us; 11us; 17us; 12us; 18us; 15us; 59us; 16us; 60us; 18us; 44us; 30us; 63us; 0us; 16404us; 0us; 16405us; 0us; 16406us; 0us; 16407us; 0us; 16408us; 5us; 16409us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 0us; 16410us; 0us; 16411us; 6us; 32768us; 13us; 56us; 14us; 57us; 15us; 54us; 16us; 55us; 17us; 58us; 19us; 62us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 4us; 32768us; 15us; 59us; 16us; 60us; 18us; 61us; 30us; 63us; 0us; 16412us; 0us; 16413us; |]
let _fsyacc_actionTableRowOffsets = [|0us; 3us; 4us; 7us; 8us; 14us; 17us; 19us; 20us; 23us; 26us; 34us; 35us; 38us; 46us; 47us; 55us; 56us; 57us; 58us; 59us; 60us; 61us; 62us; 63us; 69us; 77us; 85us; 93us; 101us; 109us; 121us; 134us; 139us; 145us; 150us; 156us; 161us; 167us; 172us; 178us; 183us; 189us; 194us; 200us; 208us; 209us; 210us; 211us; 212us; 213us; 219us; 220us; 221us; 228us; 233us; 238us; 243us; 248us; 253us; 258us; 263us; 268us; 269us; |]
let _fsyacc_reductionSymbolCounts = [|1us; 2us; 3us; 3us; 3us; 3us; 3us; 1us; 1us; 3us; 3us; 3us; 3us; 2us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 3us; 2us; 2us; 3us; 1us; |]
let _fsyacc_productionToNonTerminalTable = [|0us; 1us; 2us; 2us; 3us; 3us; 3us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 4us; 5us; 5us; 5us; 5us; 5us; 5us; 5us; 5us; 5us; |]
let _fsyacc_immediateActions = [|65535us; 49152us; 65535us; 16385us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16389us; 65535us; 16390us; 16391us; 16392us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16404us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16412us; 16413us; |]
let _fsyacc_reductions ()  =    [| 
# 279 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : command)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : '_startstart));
# 288 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : command)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 43 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                      _1 
                   )
# 43 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : command));
# 299 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : command)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 56 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                      BooleanGuard(_1,_3) 
                   )
# 56 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : gcommand));
# 311 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : gcommand)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : gcommand)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 57 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                  GCommands(_1,_3) 
                   )
# 57 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : gcommand));
# 323 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : command)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : command)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 61 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                      Commands(_1,_3) 
                   )
# 61 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : command));
# 335 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : gcommand)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 62 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                               IfStatement(_2) 
                   )
# 62 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : command));
# 346 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : gcommand)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 63 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                               DoStatement(_2) 
                   )
# 63 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : command));
# 357 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 66 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                      True 
                   )
# 66 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 367 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 67 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                       False 
                   )
# 67 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 377 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 68 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                        And(_1,_3) 
                   )
# 68 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 389 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 69 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                       Or(_1,_3) 
                   )
# 69 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 401 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 70 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                        SAnd(_1,_3) 
                   )
# 70 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 413 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 71 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                        SOr(_1,_3) 
                   )
# 71 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 425 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 72 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                               Neg(_2) 
                   )
# 72 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 436 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 73 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           Equal(_1,_3) 
                   )
# 73 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 448 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 74 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           NEqual(_1,_3) 
                   )
# 74 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 460 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 75 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           Greater(_1,_3) 
                   )
# 75 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 472 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 76 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           GreaterEqual(_1,_3) 
                   )
# 76 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 484 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 77 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           Less(_1,_3) 
                   )
# 77 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 496 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 78 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           LessEqual(_1,_3) 
                   )
# 78 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 508 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : bexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 79 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                   ParBExpr(_2) 
                   )
# 79 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : bexpr));
# 519 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 82 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           PlusExpr(_1,_3) 
                   )
# 82 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 531 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 83 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           MinusExpr(_1,_3) 
                   )
# 83 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 543 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 84 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           TimesExpr(_1,_3) 
                   )
# 84 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 555 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 85 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           DivExpr(_1,_3) 
                   )
# 85 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 567 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 86 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                           PowExpr(_1,_3) 
                   )
# 86 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 579 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 87 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                               UPlusExpr(_2) 
                   )
# 87 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 590 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 88 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                UMinusExpr(_2) 
                   )
# 88 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 601 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : aexpr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 89 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                                   ParAExpr(_2) 
                   )
# 89 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
# 612 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : float)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 90 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                                      Num(_1) 
                   )
# 90 "C:\Users\Meee\Documents\GitHub\CSM\\Task1Parser.fsp"
                 : aexpr));
|]
# 624 "C:\Users\Meee\Documents\GitHub\CSM\Task1Parser.fs"
let tables () : FSharp.Text.Parsing.Tables<_> = 
  { reductions= _fsyacc_reductions ();
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 34;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = (tables ()).Interpret(lexer, lexbuf, startState)
let start lexer lexbuf : command =
    Microsoft.FSharp.Core.Operators.unbox ((tables ()).Interpret(lexer, lexbuf, 0))
