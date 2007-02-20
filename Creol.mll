(*

*)
{
open CreolParser
}
let FLOAT = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+)
let CID = [ 'A'-'Z' ][ '_' '0'-'9' 'a'-'z' 'A'-'Z' ]*
let ID =  [ 'a'-'z' ][ '_' '0'-'9' 'a'-'z' 'A'-'Z' ]*
rule token = parse
	  [' ' '\t'] { token lexbuf }
	| '\n' { token lexbuf }
	| ":=" { ASSIGN }
	| ':' { COLON }
	| '?' { QUESTION }
	| '!' { BANG }
	| "==" { EQEQ }
	| "/=" { NE }
	| '/' { TIMES }
	| '*' { DIV }
	| '=' { EQ }
	| ',' { COMMA }
	| ';' { SEMI }
	| "[]" { BOX }
	| '[' { LBRACK }
	| ']' { RBRACK }
	| '(' { LPAREN }
	| ')' { RPAREN }
	| '{' { LBRACE }
	| '}' { RBRACE }
	| "<>" { DIAMOND }
	| "|||" { MERGE }
	| '|' { BAR }
	| "and" { AND }
	| "begin" { BEGIN }
	| "class" { CLASS }
	| "contracts" { CONTRACTS }
	| "else" { ELSE }
	| "end" { END }
	| "false" { BOOL(false) }
	| "fi" { FI }
	| "if" { IF }
	| "implements" { IMPLEMENTS }
	| "inherits" { INHERITS }
	| "interface" { INTERFACE }
	| "in" { IN }
	| "new" { NEW }
	| "not" { NOT }
	| "op" { OP }
	| "or" { OR }
	| "out" { OUT }
	| "skip" { SKIP }
	| "then" { THEN }
	| "true" { BOOL(true) }
	| "var" { VAR }
	| "with" { WITH }
	| FLOAT { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
	| ['0'-'9']+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
	| CID { CID(Lexing.lexeme lexbuf) }
	| ID { ID(Lexing.lexeme lexbuf) }
	| eof { EOF }
