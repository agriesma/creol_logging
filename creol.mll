(*

*)
{
open Creolparser
}
let FLOAT = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+) 
rule token = parse
	  [' ' '\t' '\n'] { token lexbuf }
	| "true" { BOOL(true) }
	| "false" { BOOL(false) }
	| FLOAT { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
	| ['0'-'9']+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
	| eof { EOF }
