(*

*)
{
open Parser
}
let REAL = ['0'-'9']+'.'['0'-'9']+('e' ('+'|'-')? ['0'-'9']+) 
rule token = parse
	  [' ' '\t' '\n'] { token lexbuf }
	| "true" { BOOL(true) }
	| "false" { BOOL(false) }
	| REAL { REAL(real_of_string lxm) }
	| ['0'-'9']+ { INT(int_of_string lxm) }
	| eof { EOF }
