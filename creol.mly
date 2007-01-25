%token EOF
%token CLASS CONTRACTS INHERITS IMPLEMENTS BEGIN END
%token INTERFACE WITH OP VAR IN OUT
%token EQEQ COMMA SEMI COLON ASSIGN LPAREN RPAREN
%token CHOICE MERGE
%token SKIP
%token <int>  ID
%token <int>  INT
%token PLUS TIMES
%left PLUS
%left TIMES
%start <int> main
%%

main:
	  d = declarations EOF { }
	| EOF { }

declarations:
	  declaration { }
	| declaration declarations { }

declaration:
	  classdecl	{ }
	| interfacedecl	{ }

classdecl:
	CLASS n = ID c = contracts_opt i = inherits_opt j = implements_opt
	BEGIN a = attributes m = methods_opt END { }

contracts_opt:
	  { }
	| CONTRACTS interface_name_list { }

inherits_opt:
	  { }
	| INHERITS inherits_list { }

implements_opt:
	  { }
	| IMPLEMENTS interface_name_list { }

interface_name_list:
	  ID	{ }
	| ID COMMA interface_name_list { }

inherits_list:
	  inherits { }
	| inherits COMMA inherits_list { }

inherits:
	  ID { }
	| ID LPAREN expression_list RPAREN { }

attributes:
	VAR vardecl_list	{ }

vardecl_list:
	  vardecl	{ }
	| vardecl COMMA vardecl_list	{ }

vardecl:
	  vardecl_no_init	{ }
	| vardecl_no_init ASSIGN expression	{ }

vardecl_no_init_list:
	  vardecl_no_init	{ }
	| vardecl_no_init COMMA vardecl_no_init_list	{ }

vardecl_no_init:
	  i = ID COLON t = ID { }

method_decl:
	  WITH m = ID OP i = ID p = parameters_opt { }
	| OP i = ID p = parameters_opt { }

parameters_opt:
	  (* empty *) { }
	| LPAREN inputs RPAREN { }
	| LPAREN outputs RPAREN { }
	| LPAREN inputs SEMI outputs RPAREN { }

inputs:
	IN vardecl_no_init_list { }

outputs:
	OUT vardecl_no_init_list { }

method_def:
	d = method_decl EQEQ s = statement { }

methods_opt:
	  (* empty *) { [] }
	| m = methods { m }

methods:
	| m = method_def { [m] }
	| m = method_def l = methods { m::l }

interfacedecl:
	  INTERFACE n = ID inherits_opt BEGIN m = method_decls_opt END { }

method_decls_opt:
	  (* empty *)		{ [] }
	| m = method_decls	{ m }

method_decls:
	| m = method_decl { [m] }
	| m = method_decl l = method_decls { m::l }

(*
 Statements
 *)
statement:
	s = choice_statement { s }

choice_statement:
	s = merge_statement { s }
	| l = merge_statement CHOICE r = choice_statement { }

merge_statement:
	  s = compound_statement { s }
	| l = compound_statement MERGE r = merge_statement { }

compound_statement:
	  s = basic_statement { s }
	| l = basic_statement SEMI r = compound_statement { }

basic_statement:
	  SKIP { }
	| LPAREN s = statement RPAREN { s }

expression_list:
	  e = expression	{ [e] }
	| e = expression COMMA l = expression_list { e::l }

expression:
	| i = INT { i }
	| l = expression PLUS r = expression { r + l }
	| l = expression TIMES r = expression { r + l }
