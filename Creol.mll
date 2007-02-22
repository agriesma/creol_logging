(*

*)
{
open CreolParser
}
let FLOAT = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+)
let CID = [ 'A'-'Z' ][ 'a'-'z' 'A'-'Z' ]*
let ID =  [ 'a'-'z' ][ 'a'-'z' 'A'-'Z' '0'-'9' ]*
let STRING = '"' [^ '\n' '"' ]* '"'
rule token = parse
	  [' ' '\t'] { token lexbuf }
	| '\n' { token lexbuf }
	| ":=" { ASSIGN }
	| ':' { COLON }
	| '?' { QUESTION }
	| '!' { BANG }
	| "==" { EQEQ }
	| "<=" { LE }
	| ">=" { GE }
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
(*	| ".." { DOTDOT } *)
	| '.' { DOT }
	| "[]" { BOX }
	| '[' { LBRACK }
	| ']' { RBRACK }
	| '(' { LPAREN }
	| ')' { RPAREN }
	| '{' { LBRACE }
	| '}' { RBRACE }
(*	| "<>" { DIAMOND } *)
	| "|||" { MERGE }
(*	| '|' { BAR } *)
	| "and" { AND }
	| "await" { AWAIT }
	| "begin" { BEGIN }
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
	| "in" { IN }
	| "new" { NEW }
	| "nil" { NIL }
	| "not" { NOT }
	| "op" { OP }
	| "or" { OR }
	| "out" { OUT }
	| "skip" { SKIP }
	| "then" { THEN }
	| "true" { BOOL(true) }
	| "var" { VAR }
	| "wait" { WAIT }
	| "with" { WITH }
	| "xor" { XOR }
	| "length" { BUILTIN(Lexing.lexeme lexbuf) }
	| FLOAT { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
	| ['0'-'9']+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
	| CID { CID(Lexing.lexeme lexbuf) }
	| ID { ID(Lexing.lexeme lexbuf) }
	| STRING { let s = Lexing.lexeme lexbuf in STRING(String.sub s 1 (String.length s - 1)) }
	| eof { EOF }
