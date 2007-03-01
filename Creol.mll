(*

*)
{
open CreolParser
open Lexing

exception Reserved of string * int * string

let update_loc lexbuf =
  let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

let reserved lexbuf =
  let pos = lexbuf.lex_curr_p in
    let tok = Lexing.lexeme lexbuf in
      raise (Reserved (pos.pos_fname, pos.pos_lnum, tok))
}
let COMMENT = '/' '/' [ ^ '\n' ]*
let FLOAT = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+)
let CID = [ 'A'-'Z' ][ 'a'-'z' 'A'-'Z' ]*
let ID =  [ 'a'-'z' ][ 'a'-'z' 'A'-'Z' '0'-'9' ]*
let STRING = '"' [^ '\n' '"' ]* '"'
rule token = parse
      [' ' '\t'] { token lexbuf }
    | COMMENT { token lexbuf }
    | "/*" { c_style_comment lexbuf }
    | '\n' { update_loc lexbuf; token lexbuf }
    | ":=" { ASSIGN }
    | "::" { reserved lexbuf }
    | '_' { reserved lexbuf }
    | ':' { COLON }
    | '?' { QUESTION }
    | '!' { BANG }
    | "@@" { reserved lexbuf }
    | '@' { AT }
    | '#' { reserved lexbuf }
    | "==" { EQEQ }
    | "<=" { LE }
    | ">=" { GE }
    | ">>" { reserved lexbuf }
    | "<<" { reserved lexbuf }
    | "<" { LT }
    | ">" { GT }
    | "/=" { NE }
    | '*' { TIMES }
    | '/' { DIV }
    | '+' { PLUS }
    | '-' { MINUS }
    | '=' { EQ }
    | ',' { COMMA }
    | ';' { SEMI }
    | ".." { reserved lexbuf }
    | '.' { DOT }
    | "[]" { BOX }
    | '[' { LBRACK }
    | ']' { RBRACK }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '{' { LBRACE }
    | '}' { RBRACE }
    | "<>" { reserved lexbuf }
    | "|||" { MERGE }
    | "||" { reserved lexbuf }
    | "|" { reserved lexbuf }
    | "and" { AND }
    | "await" { AWAIT }
    | "begin" { BEGIN }
    | "caller" { ID("caller") (* XXX: Should be special *) }
    | "class" { CLASS }
    | "contracts" { CONTRACTS }
    | "else" { ELSE }
    | "end" { END }
    | "false" { BOOL(false) }
    | "fi" { FI }
    | "iff" { IFF }
    | "if" { IF }
    | "implements" { IMPLEMENTS }
    | "inherits" { INHERITS }
    | "interface" { INTERFACE }
    | "inv" { reserved lexbuf }
    | "in" { IN }
    | "new" { NEW }
    | "nil" { NIL }
    | "null" { NULL }
    | "not" { NOT }
    | "op" { OP }
    | "or" { OR }
    | "out" { OUT }
    | "pre" { reserved lexbuf }
    | "post" { reserved lexbuf }
    | "skip" { SKIP }
    | "then" { THEN }
    | "this" { ID("this") (* XXX: Should be special, too. *) }
    | "true" { BOOL(true) }
    | "var" { VAR }
    | "wait" { WAIT }
    | "with" { WITH }
    | "xor" { XOR }
    | FLOAT { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
    | ['0'-'9']+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
    | CID { CID(Lexing.lexeme lexbuf) }
    | ID { ID(Lexing.lexeme lexbuf) }
    | STRING { let s = Lexing.lexeme lexbuf in STRING(String.sub s 1 ((String.length s) - 2)) }
    | eof { EOF }
and c_style_comment = parse
      "*/"	{ token lexbuf }
    | '\n' { update_loc lexbuf; c_style_comment lexbuf }
    | '*' { c_style_comment lexbuf }
    | [ ^ '\n' '*'] * { c_style_comment lexbuf }
