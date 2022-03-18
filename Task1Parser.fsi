// Signature file for parser generated by fsyacc
module Task1Parser
type token = 
  | SKIP
  | LBRA
  | RBRA
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
  | VAR of (string)
  | NUM of (int)
type tokenId = 
    | TOKEN_SKIP
    | TOKEN_LBRA
    | TOKEN_RBRA
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
    | TOKEN_VAR
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_gc
    | NONTERM_command
    | NONTERM_bexpression
    | NONTERM_aexpression
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (command) 
