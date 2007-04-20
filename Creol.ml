(*
 * Creol.ml -- Definition and manipulation of Creol AST
 *
 * This file is part of creolcomp
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

module Note =
  struct

    type type_info = {
      attribute: bool;
      label: bool;
      defined: bool;
      life: bool;
    }

    module Environment = Map.Make(String)

    let empty = Environment.empty

    type t = { file: string; line: int; env: type_info Environment.t }

    let make pos = {
      file = pos.Lexing.pos_fname ;
      line = pos.Lexing.pos_lnum;
      env = empty
    }

    let line { file = _ ; line = l; env = _ } = l

    let file { file = f ; line = _; env = _ } = f

    let to_xml writer { file = f; line = l; env = d } =
      XmlTextWriter.start_element writer "note";
      XmlTextWriter.write_attribute writer "file" f ;
      XmlTextWriter.write_attribute writer "line" (string_of_int l) ;
      Environment.iter (function elt ->
	function note ->
	  XmlTextWriter.start_element writer "defined" ;
	  XmlTextWriter.write_attribute writer "name" elt ;
	  XmlTextWriter.write_attribute writer "attribute"
	    (string_of_bool note.attribute) ;
	  XmlTextWriter.write_attribute writer "label"
	    (string_of_bool note.label) ;
	  XmlTextWriter.write_attribute writer "defined"
	    (string_of_bool note.defined) ;
	  XmlTextWriter.write_attribute writer "life"
	    (string_of_bool note.life) ;
	  XmlTextWriter.end_element writer) d;
      XmlTextWriter.end_element writer

    module Vars = Set.Make(String)

    let domain env =
      Environment.fold (fun k _ set -> Vars.add k set) env Vars.empty

    let join left right =
      let dom = Vars.union (domain left) (domain right) in
	Vars.fold
	  (fun k r ->
	    match (Environment.mem k left, Environment.mem k right) with
		(true, true) ->
		  let nl = Environment.find k left
		  and nr = Environment.find k right
		  in Environment.add
		    k
		    { attribute = nl.attribute && nr.attribute;
		      label = nl.label && nr.label ;
		      defined = nl.defined || nr.defined;
		      life = nl.life || nr.life }
		    r
	      | (true, false) -> Environment.add k (Environment.find k left) r
	      | (false, true) -> Environment.add k (Environment.find k right) r
	      | (false, false) -> assert false)
	  dom Environment.empty
	
    let meet left right =
      let dom = Vars.union (domain left) (domain right) in
	Vars.fold
	  (fun k r ->
	    match (Environment.mem k left, Environment.mem k right) with
		(true, true) ->
		  let nl = Environment.find k left
		  and nr = Environment.find k right
		  in Environment.add
		    k
		    { attribute = nl.attribute && nr.attribute;
		      label = nl.label && nr.label ;
		      defined = nl.defined || nr.defined;
		      life = nl.life || nr.life }
		    r
	      | (true, false) -> Environment.add k (Environment.find k left) r
	      | (false, true) -> Environment.add k (Environment.find k right) r
	      | (false, false) -> assert false)
	  dom Environment.empty
	
  end

module Type =
  struct
    type t =
	Basic of string
	| Application of string * t list
	| Variable of string
	| Label

    (* These are the support functions for the abstract syntax tree. *)

    let rec as_string =
      function
	  Basic s -> s
	| Application (s, p) ->
	    s ^ "[" ^ (string_of_creol_type_list p) ^ "]"
	| Variable s -> "$" ^ s
	| Label -> "/* Label */"
    and string_of_creol_type_list =
      function
	  [t] -> as_string t
	| t::l -> (as_string t) ^ ", " ^
	    (string_of_creol_type_list l)
	| [] -> assert false (* Silence a compiler warning. *)
  end

module Pattern =
struct
  type ('a, 'b, 'c) t =
    { pattern: 'a; when_clause: 'b option; match_clause: 'c }
end

module Case =
struct
  type ('a, 'b, 'c, 'd) t =
    { what: 'a; cases: ('b, 'c, 'd) Pattern.t list }
end

module Try =
struct
  type ('a, 'b, 'c, 'd) t =
    { what: 'a; catches: ('b, 'c, 'd) Pattern.t list }
end

module Expression =
  struct
    
    type 'a t =
	Null of 'a
	| Nil of 'a
	| Bool of 'a * bool
	| Int of 'a * int
	| Float of 'a * float
	| String of 'a * string
	| Id of 'a * string
	| Cast of 'a * 'a t * Type.t
	| Index of 'a * 'a t * 'a t
        | FieldAccess of 'a * 'a t * string
	| Unary of 'a * unaryop * 'a t
	| Binary of 'a * binaryop * 'a t * 'a t
	| If of 'a * 'a t * 'a t * 'a t
	| Case of 'a * ('a t, unit, 'a t, 'a t) Case.t
	| Typecase of 'a * ('a t, Type.t, 'a t, 'a t) Case.t
	| FuncCall of 'a * string * 'a t list
	| Wait of 'a
	| Label of 'a * string
	| New of 'a * Type.t * 'a t list
    and unaryop =
	Not
	| UMinus
	| Length
    and binaryop =
	Plus
	| Minus
	| Times
	| Div
	| Modulo
	| Exponent
	| Eq
	| Ne
	| Le
	| Lt
	| Ge
	| Gt
	| And
	| Or
	| Xor
	| Implies
	| Iff
	| LAppend
	| RAppend
	| Concat
	| Project
	| In
	| GuardAnd

    let string_of_binaryop =
      function
	  Plus -> "+"
	| Minus -> "-"
	| Times -> "*"
	| Div -> "/"
	| Eq -> "="
	| Ne -> "/="
	| Le -> "<="
	| Lt -> "<"
	| Ge -> ">="
	| Gt -> ">"
	| And -> "&&"
	| Or -> "||"
	| Xor -> "^"
	| Iff -> "<=>"
	| LAppend -> "|-"
	| RAppend -> "-|"
	| Concat -> "|-|"
	| Project -> "\\"
	| GuardAnd -> "&"

    let prec_of_binaryop =
      function
	  Plus -> (33, 33)
	| Minus -> (33, 33)
	| Times -> (31, 31)
	| Div -> (31, 31)
	| Eq -> (51, 51)
	| Ne -> (51, 51)
	| Le -> (37, 37)
	| Lt -> (37, 37)
	| Ge -> (37, 37)
	| Gt -> (37, 37)
	| And -> (55, 55)
	| Or -> (59, 59)
	| Xor -> (57, 57)
	| Iff -> (51, 51)
	| LAppend -> (33, 33)
	| RAppend -> (33, 33)
	| Concat -> (33, 33)
	| Project -> (35, 35)
	| GuardAnd -> (61, 61)

    let string_of_unaryop =
      function
	  Not -> "not"
	| UMinus -> "-"
	| Length -> "#"

    let prec_of_unaryop =
      function
	  Not -> 53
	| UMinus -> 15
	| Length -> 15

  end

open Expression

module Statement =
  struct
    type ('a, 'b) t =
	Skip of 'a
	| Assert of 'a * 'b Expression.t
	| Prove of 'a * 'b Expression.t
	| Assign of 'a * string list * 'b Expression.t list
	| Await of 'a * 'b Expression.t
	| AsyncCall of 'a * string option * 'b Expression.t * string *
	    'b Expression.t list
	| Reply of 'a * string * string list
	| Free of 'a * string
	| SyncCall of 'a * 'b Expression.t * string *
	    'b Expression.t list * string list
	| LocalAsyncCall of 'a * string option * string * string option *
	    string option * 'b Expression.t list
	| LocalSyncCall of 'a * string * string option * string option *
            'b Expression.t list * string list
	| Tailcall of 'a * string * string option * string option *
	    'b Expression.t list
	| If of 'a * 'b Expression.t * ('a, 'b) t * ('a, 'b)t
	| While of 'a * 'b Expression.t * 'b Expression.t option * ('a, 'b) t
	| For of 'a * string * 'b Expression.t * 'b Expression.t *
	    'b Expression.t option * 'b Expression.t option * ('a, 'b) t
	| Raise of 'a * string * 'b Expression.t list
	| Try of 'a * ('a, 'b) t * ('a, 'b) catcher list
        | Case of 'a *
	    ('b Expression.t, unit, 'b Expression.t, ('a, 'b) t) Case.t
	| Typecase of 'a *
	    ('b Expression.t, Type.t, 'b Expression.t, ('a, 'b) t) Case.t
	| Sequence of 'a * ('a, 'b) t list
	| Merge of 'a * ('a, 'b) t * ('a, 'b) t
	| Choice of 'a * ('a, 'b) t * ('a, 'b)t
    and ('a, 'b) catcher =
	{ catch: string option;
	  catch_parameters: string list;
	  catch_statement: ('a, 'b) t }
    and ('a, 'b) typecase =
	{ with_type: Type.t option; with_statement: ('a, 'b) t }

    let note =
      function
	  Skip a -> a
	| Assert (a, _) -> a
	| Prove (a, _) -> a
	| Assign (a, _, _) -> a
	| Await (a, _) -> a
	| AsyncCall (a, _, _, _, _) -> a
	| Reply (a, _, _) -> a
	| Free (a, _) -> a
	| SyncCall (a, _, _, _, _) -> a
	| LocalAsyncCall (a, _, _, _, _, _) -> a
	| LocalSyncCall (a, _, _, _, _, _) -> a
	| Tailcall (a, _, _, _, _) -> a
	| If (a, _, _, _) -> a
	| While (a, _, _, _) -> a
	| For (a, _, _, _, _, _, _) -> a
	| Raise (a, _, _) -> a
	| Try (a, _, _) -> a
	| Case (a, _) -> a
	| Typecase (a, _) -> a
	| Sequence(a, _) -> a
	| Merge(a, _, _) -> a
	| Choice(a, _, _) -> a

  end

open Statement

(** The abstract syntax of Creol *)
type 'a creol_vardecl =
    { var_name: string; var_type: Type.t; var_init: 'a Expression.t option }

type ('a, 'b) creolmethod =
    { meth_name: string;
      meth_inpars: 'b creol_vardecl list;
      meth_outpars: 'b creol_vardecl list;
      meth_vars: 'b creol_vardecl list;
      meth_body: ('a, 'b) Statement.t option }





module With = struct

  type ('a, 'b) t = {
    co_interface: string option;
    methods: ('a, 'b) creolmethod list;
    invariants: 'b Expression.t list
  }

end





module Class =
struct

  type 'a inherits = string * ('a Expression.t list)

  type ('a, 'b) t =
      { name: string;
	parameters: 'b creol_vardecl list;
	inherits: 'b inherits list;
	contracts: string list;
	implements: string list;
	attributes: 'b creol_vardecl list;
	with_defs: ('a, 'b) With.t list }

end





module Interface =
struct

  type  ('a, 'b) t =
      { name: string;
	inherits: string list;
	with_decl: ('a, 'b) With.t option }

end

module Exception =
struct
  type 'b t = { name: string; parameters: 'b creol_vardecl list }
end





module Datatype =
struct

  type ('a, 'b) t = {
    name: string
  }

end





module Declaration =
struct

  type ('a, 'b) t =
      Class of ('a, 'b) Class.t
      | Interface of ('a, 'b) Interface.t
      | Datatype of ('a, 'b) Datatype.t
      | Exception of 'b Exception.t

end

open Declaration






(** Normalise an abstract syntax tree by replacing all derived concepts
    with there basic equivalents *)
let rec simplify_expression =
  function
      Unary(a, Not, e) -> FuncCall(a, "not", [simplify_expression e])
    | Unary(a, UMinus, e) -> FuncCall(a, "neg", [simplify_expression e])
    | Binary(a, Plus, l, r) -> FuncCall(a, "plus", [simplify_expression l; simplify_expression r])
    | Binary(a, Minus, l, r) -> FuncCall(a, "minus", [simplify_expression l; simplify_expression r])
    | Binary(a, Times, l, r) -> FuncCall(a, "times", [simplify_expression l; simplify_expression r])
    | Binary(a, Div, l, r) -> FuncCall(a, "div", [simplify_expression l; simplify_expression r])
    | Binary(a, Le, l, r) -> FuncCall(a, "lessEq", [simplify_expression l; simplify_expression r])
    | Binary(a, Lt, l, r) -> FuncCall(a, "less", [simplify_expression l; simplify_expression r])
    | Binary(a, Ge, l, r) -> FuncCall(a, "lessEq", [simplify_expression r; simplify_expression l])
    | Binary(a, Gt, l, r) -> FuncCall(a, "less", [simplify_expression r; simplify_expression l])
    | Binary(a, Eq, l, r) -> FuncCall(a, "equal", [simplify_expression l; simplify_expression r])
    | Binary(a, Ne, l, r) -> FuncCall(a, "not", [FuncCall(a, "equal", [simplify_expression l; simplify_expression r])])
    | Binary(a, And, l, r) -> FuncCall(a, "and", [simplify_expression l; simplify_expression r])
    | Binary(a, Iff, l, r) -> FuncCall(a, "equal", [simplify_expression l; simplify_expression r])
    | Binary(a, Or, l, r) -> FuncCall(a, "or", [simplify_expression l; simplify_expression r])
    | Binary(a, Xor, l, r) -> FuncCall(a, "not", [FuncCall(a, "equal", [simplify_expression l; simplify_expression r])])
    | Binary(a, GuardAnd, l, r) -> Binary(a, GuardAnd, simplify_expression l,
	simplify_expression r)
    | FuncCall(a, f, args) -> FuncCall(a, f, List.map simplify_expression args)
    | New (a, t, p) -> New (a, t, List.map simplify_expression p)
    | t -> t
and simplify_statement =
  function
      Skip a -> Skip a
    | Assert (a, e) -> Assert (a, simplify_expression e)
    | Prove (a, e) -> Prove (a, simplify_expression e)
    | Assign (a, s, e) -> Assign (a, s, List.map simplify_expression e)
    | Await (a, g) -> Await (a, simplify_expression g)
    | AsyncCall (a, l, e, n, p) ->
	AsyncCall (a, l, simplify_expression e, n,
		  List.map simplify_expression p)
    | Free (a, l) -> Free (a, l)
    | Reply (a, l, v) -> Reply (a, l, v)
    | SyncCall (a, e, n, p, r) ->
	SyncCall (a, simplify_expression e, n, List.map simplify_expression p, r)
    | LocalAsyncCall (a, l, m, lb, ub, i) ->
	LocalAsyncCall (a, l, m, lb, ub, List.map simplify_expression i)
    | LocalSyncCall (a, m, l, u, i, o) ->
	LocalSyncCall (a, m, l, u, List.map simplify_expression i, o)
    | Tailcall (a, m, l, u, i) ->
	Tailcall (a, m, l, u, List.map simplify_expression i)
    | If (a, c, t, f) -> If(a, simplify_expression c, simplify_statement t,
			   simplify_statement f)
    | While (a, c, None, b) ->
	While (a, simplify_expression c, None, simplify_statement b)
    | While (a, c, Some i, b) ->
	While (a, simplify_expression c, Some (simplify_expression i),
	       simplify_statement b)
    | Sequence (a, s1) -> Sequence (a, List.map simplify_statement s1)
    | Merge (a, s1, s2) -> Merge (a, simplify_statement s1,
				 simplify_statement s2)
    | Choice (a, s1, s2) -> Choice (a, simplify_statement s1,
				   simplify_statement s2)
and simplify_method_variables note =
  (** Compute a pair of a new list of local variable declarations
      and a list of assignments used for initialisation. *)
  function
      [] -> ([], [])
    | ({ var_name = _ ; var_type = _ ; var_init = None } as v)::l ->
	let r = simplify_method_variables note l in
	  (v::(fst r), snd r)
    | ({ var_name = n; var_type = _ ; var_init = Some i } as v)::l ->
	let r = simplify_method_variables note l in
	let a = Assign(note, [n], [simplify_expression i]) in
	  ({ v with var_init = None}::(fst r), a::(snd r))
and simplify_method m =
  (** Simplify a method definition. *)
  match m.meth_body with
    None -> m
  | Some mb  ->
	let mv = m.meth_vars in
	let note = Statement.note mb in
	let smv = simplify_method_variables note mv in
	let smb = simplify_statement mb in
	{ m with meth_vars = fst smv ; meth_body =
	  Some (begin
	    match smb with
	      Sequence (n, sl) -> Sequence (n, (snd smv)@ sl)
	    | s -> Sequence (note, (snd smv)@[s])
	  end) }
and simplify_with w =
  { w with With.methods = List.map simplify_method w.With.methods }
and simplify_inherits =
  function
      (n, e) -> (n, List.map simplify_expression e)
and simplify_inherits_list =
  function
      [] -> []
    | i::l -> (simplify_inherits i)::(simplify_inherits_list l)
and simplify_class c =
  { c with Class.inherits = simplify_inherits_list c.Class.inherits;
    Class.with_defs = List.map simplify_with c.Class.with_defs }
and simplify_interface i =
  i
and simplify =
  function
      [] -> []
    | Class c::l -> (Class (simplify_class c))::(simplify l)
    | Interface i::l -> (Interface (simplify_interface i))::(simplify l)
    | Exception e::l -> (Exception e)::(simplify l)
    | Datatype d::l -> (Datatype d)::(simplify l)

let collect_declarations attribute =
    List.fold_left
	(function map ->
	  function { var_name = name; var_type = _; var_init = _ } -> 
            Note.Environment.add name
	      { Note.attribute = attribute;
		Note.label = false;
		(* The value of an attribute is always defined *)
		Note.defined = attribute;
		(* The value of an attribute is always life *)
		Note.life = attribute }
	      map)
	Note.Environment.empty

let rec find_definitions l =
  (** Computes the definitions of a variable.

  *)
  List.map definitions_in_declaration l
and definitions_in_declaration =
  function
      Class c -> Class (definitions_in_class c)
    | Interface i -> Interface (definitions_in_interface i)
    | Exception e -> Exception e
    | Datatype d -> Datatype d (* XXX *)
and definitions_in_class c =
  let attrs = collect_declarations true
    (c.Class.parameters @ c.Class.attributes) in
    { c with
      Class.with_defs = List.map (definitions_in_with attrs) c.Class.with_defs }
and definitions_in_interface i =
  i
and definitions_in_with attrs w =
  { w with
    With.methods = List.map (definitions_in_method attrs) w.With.methods }
and definitions_in_method attrs m =
  match m.meth_body with
      None -> m
    | Some body ->
	{ m with meth_body =
	    let note =
	      { Note.file = Note.file (Statement.note body);
		Note.line = Note.line (Statement.note body);
		Note.env = attrs }
	    in
	      Some (definitions_in_statement note body) }
and definitions_in_statement note stm =
  (** Compute the variables defined at a current statement.

      @param attrs is the set of names which are attributes.  They are always
      defined in a program.

      @param note is the updated note of the preceding statement.

      @return The statement with its note updated.  *)
  let define env name label =
    (** Define a name in an environment. *)
    let v =
      { Note.attribute = false;
	Note.label = label;
	Note.defined = true;
	Note.life = false }
    in
      Note.Environment.add name v env
  in
    match stm with
	Skip n ->
	  Skip { n with Note.env = note.Note.env }
      | Assert (n, e) ->
	  Assert ({ n with Note.env = note.Note.env }, e)
      | Prove (n, e) ->
	  Prove ({ n with Note.env = note.Note.env }, e)
      | Assign (n, lhs, rhs) ->
	  Assign ({ n with Note.env = 
	      List.fold_left (fun e n -> define e n false)
		note.Note.env lhs}, lhs, rhs) (* XXX *)
      | Await (n, g) ->
	  Await ({ n with Note.env = note.Note.env }, g)
      | AsyncCall (n, None, c, m, a) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  AsyncCall ({ n with Note.env = note.Note.env }, None, c, m, a)
      | AsyncCall (n, Some l, c, m, a) ->
	  AsyncCall ({ n with Note.env = (define note.Note.env l true) },
		    Some l, c, m, a)
      | Reply (n, l, p) ->
	  Reply ({ n with Note.env = List.fold_left
	      (fun e n -> define e n false) note.Note.env p } , l, p)
| Free (n, v) -> assert false
| SyncCall (n, c, m, ins, outs) ->
    SyncCall ({ n with Note.env = note.Note.env }, c, m, ins, outs) (* XXX *)
| LocalAsyncCall (n, None, m, ub, lb, i) ->
    (* XXX: This should not happen, but if we resolve this, we need to
       rerun this for updating the chain... *)
    LocalAsyncCall ({ n with Note.env = note.Note.env}, None, m, ub, lb,
		   i)
| LocalAsyncCall (n, Some l, m, ub, lb, i) ->
    LocalAsyncCall ({ n with Note.env = (define note.Note.env l true)},
		   Some l, m, ub, lb, i)
| LocalSyncCall (n, m, u, l, a, r) ->
    LocalSyncCall ({ n with Note.env = note.Note.env },
		  m, u, l, a, r) (* XXX *)
| Tailcall (n, m, u, l, a) -> assert false
| If (n, c, l, r) ->
    (* Beware, that the new note essentially contains the union
       of the definitions of both its branches, whereas the first
       statement of each branch contains the updated note of the
       preceding statement. *)
    let nl = (definitions_in_statement note l)
    and nr = (definitions_in_statement note r) in
      If ({n with Note.env = Note.join (Statement.note nl).Note.env
	  (Statement.note nr).Note.env},
	 c, nl, nr)
| While (n, c, i, b) ->
    While ({ n with Note.env = note.Note.env }, c, i,
	  definitions_in_statement n b)
| Sequence (n, l) ->
    let rec definitions_in_sequence np =
      function
	  [] -> assert false;
	| [s] -> [definitions_in_statement np s]
	| s::r -> let ns = definitions_in_statement np s in
	  let nr = definitions_in_sequence (Statement.note ns) r in
	    ns::nr
    in
    let nl = definitions_in_sequence note l in
      Sequence({ n with Note.env =
	  (Statement.note (List.nth nl ((List.length nl) - 1))).Note.env},
	      nl)
	(* For merge and choice we do not enforce sequencing of the
	   computation of the parts, but we allow the compiler to
	   choose some order *)
| Merge (n, l, r) -> 
    let nl = (definitions_in_statement note l)
    and nr = (definitions_in_statement note r) in
      Merge ({n with Note.env = Note.join (Statement.note nl).Note.env
	  (Statement.note nr).Note.env},
	    nl, nr)
| Choice (n, l, r) -> 
    let nl = (definitions_in_statement note l)
    and nr = (definitions_in_statement note r) in
      Choice ({n with Note.env = Note.join (Statement.note nl).Note.env
	  (Statement.note nr).Note.env},
	     nl, nr)

let rec life_variables tree =
  (** Compute whether a variable is still in use at a position in the
      program.

      The algorithm assumes that the input [tree] has been annotated with
      information about the definitions of variables.  See
      [find_definitions].

      It will perform a back-ward pass and annotate each node with the
      use-information.

      This algorithms has been adapted from the algorithm described in
      Section 9.5 "Next-Use Information" of A.V. Aho, R. Sethi, and J.D.
      Ullman, "Compilers: Principles, Techniques, and Tools",
      Addison-Wesley, 1986.

      Where this algorithm comes from is not clear to me, but it may already
      be mentioned in Knuth, Donald E. (1962), "A History of Writing
      Compilers," Computers and Automation,, December, 1962, reprinted in
      Pollock, Barry W., ed. Compiler Techniques, Auerbach Publishers,
      1972. *)
  List.map uses_in_declaration tree
and uses_in_declaration =
  function
    Class c -> Class (uses_in_class c)
  | Interface i -> Interface (uses_in_interface i)
  | Exception e -> Exception e
  | Datatype d -> Datatype d (* XXX *)
and uses_in_class c =
  { c with Class.with_defs = List.map uses_in_with c.Class.with_defs }
and uses_in_interface i =
  i
and uses_in_with w =
  { w with With.methods = List.map uses_in_method w.With.methods }
and uses_in_method m =
  match m.meth_body with
      None -> m
    | Some body -> { m with meth_body = Some (uses_in_statement body) }
and uses_in_statement =
  function
      Skip _ as s -> s
    | Assert (_, _) as s -> s
    | Prove (_, _) as s -> s
    | Assign (a, l, r) -> assert false
    | Await (a, g) -> assert false
    | AsyncCall (a, None, c, m, ins) -> assert false
    | AsyncCall (a, Some l, c, m, ins) -> assert false
    | Reply (a, l, outs) -> assert false (* use l and clear p *)
    | Free (a, v) -> assert false
    | SyncCall (a, c, m, ins, outs) -> assert false
    | LocalAsyncCall (a, None, m, lb, ub, ins) -> assert false
    | LocalAsyncCall (a, Some l, m, lb, ub, ins) -> assert false
    | LocalSyncCall (a, m, lb, ub, ins, outs) -> assert false
    | Tailcall (a, m, lb, ub, ins) -> assert false
    | If (a, c, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	let nc = uses_in_expression c in
	  If ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
	     nc, ns1, ns2)
    | While (a, c, i, b) -> assert false
    | Sequence (a, sl) ->
	let nsl = uses_in_sequence a sl in
	  Sequence ({ a with Note.env =
	      (Statement.note (List.nth nsl
				  ((List.length nsl) - 1))).Note.env}, nsl)
    | Merge (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Merge ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		ns1, ns2)
    | Choice (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Choice ({ a with 
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		 ns1, ns2)
and uses_in_sequence note =
  function
      [] -> assert false
    | [s] -> assert false
    | s::r ->
	let nr = uses_in_sequence note r in
	let ns = uses_in_statement s in
	  ns::nr
and uses_in_expression e = e



let tailcall_counter = ref 0

let tailcall_successes () = !tailcall_counter

let optimise_tailcalls prg =
  (** Take a program and try to replace tail calls with a version using
      out special macro. *)
  let rec optimise_declaration =
    function
      Class c -> Class (optimise_in_class c)
    | Interface i -> Interface i
    | Exception e -> Exception e
    | Datatype d -> Datatype d
  and optimise_in_class c =
    { c with Class.with_defs = List.map optimise_in_with c.Class.with_defs }
  and optimise_in_with w =
    { w with With.methods = List.map optimise_in_method w.With.methods }
  and optimise_in_method m =
    match m.meth_body with
	None -> m
      | Some body ->
	  { m with meth_body =
	      Some ((optimise_in_statement
			(List.map (function v -> v.var_name) m.meth_outpars))
		       body) } 
  and optimise_in_statement outs =
    function
	Sequence (a, sl) ->
	  Sequence (a, optimise_in_statement_inner outs sl)
      | s -> s
  and optimise_in_statement_inner outs =
    function
	[] -> assert false
      | [LocalSyncCall(ia, m, lb, ub, i, o)] when o = outs ->
	  tailcall_counter := !tailcall_counter + 1;
	  [LocalSyncCall(ia, m, lb, ub, i, o)]
      | [s] -> [s]
      | s::l -> s::(optimise_in_statement_inner outs l)
  in
    tailcall_counter := 0;
    List.map optimise_declaration prg





let rec separated_list elt_fun sep_fun =
  (** Helper function for outputting a separated list.
      It will call [elt_fun] for each element of the list and
      [sep_fun] between each element, *)
  function
      [] -> ()
    | [s] -> elt_fun s
    | s::r ->
	elt_fun s;
	sep_fun ();
	separated_list elt_fun sep_fun r

let rec pretty_print out list =
  separated_list (pretty_print_declaration out)
    (function () -> output_string out "\n\n") list;
  output_string out "\n";
  flush out
and pretty_print_declaration out_channel =
  function
      Class c -> pretty_print_class out_channel c
    | Interface i -> pretty_print_iface out_channel i
    | Exception e -> pretty_print_exception out_channel e
    | Datatype d -> pretty_print_datatype out_channel d
and pretty_print_datatype out_channel d =
  output_string out_channel ("datatype " ^ d.Datatype.name ^ "\n");
  output_string out_channel "begin\n" ;
  output_string out_channel "end\n"
and pretty_print_exception out_channel e =
  output_string out_channel ("exception " ^ e.Exception.name) ;
  begin
    match e.Exception.parameters with
        [] -> ()
      | l -> output_string out_channel "(";
	  pretty_print_vardecls out_channel 0 "" ", " "" l;
	  output_string out_channel ")" 
  end ;
  output_string out_channel "\n"
and pretty_print_iface out_channel i =
  output_string out_channel "interface ";
  output_string out_channel i.Interface.name;
  output_string out_channel "\nbegin\n";  
  output_string out_channel "end"
and pretty_print_class out_channel c =
  output_string out_channel ("class " ^ c.Class.name ^ " ") ;
  ( match c.Class.parameters with
	[] -> ()
      | l -> output_string out_channel "(";
	  pretty_print_vardecls out_channel 0 "" ", " "" l;
	  output_string out_channel ")" ) ;
  ( match c.Class.inherits with
	[] -> ()
      | l -> output_string out_channel "\ninherits ";
	  separated_list (pretty_print_inherits out_channel)
	    (function () -> output_string out_channel ", ") l) ;
  ( match c.Class.contracts with
	[] -> ()
      | l -> output_string out_channel "\ncontracts " );
  if [] <> c.Class.implements then
    begin
      output_string out_channel "\nimplements " ;
      separated_list (output_string out_channel)
	(function () -> output_string out_channel ", ") c.Class.implements;
    end;
  do_indent out_channel 0;
  output_string out_channel "begin";
  if [] <> c.Class.attributes then
    begin
      do_indent out_channel 1 ;
      pretty_print_vardecls out_channel 1 "var " "" "\n" c.Class.attributes;
      output_string out_channel "\n";
    end;
  if [] <> c.Class.with_defs then
    begin
      List.iter (pretty_print_with out_channel) c.Class.with_defs ;
    end ;
  if [] = c.Class.attributes && [] = c.Class.with_defs then
    output_string out_channel "\n";
  output_string out_channel "end"
and pretty_print_inherits out_channel (inh, args) =
  output_string out_channel inh;
  if args <> [] then
    begin
      output_string out_channel "(";
      separated_list (pretty_print_expression out_channel)
	(function () -> output_string out_channel ", ") args;
      output_string out_channel ")"
    end
and pretty_print_with out_channel w =
  let indent = if w.With.co_interface = None then 1 else 2
  in
    begin
      match w.With.co_interface with
	  None -> ()
	| Some c ->
	    do_indent out_channel 1;
	    output_string out_channel ("with " ^ c);
    end ;
    do_indent out_channel indent;
    pretty_print_methods out_channel indent w.With.methods
      (* XXX: Take care of invariants later *)
and pretty_print_methods out_channel indent list =
  separated_list
    (pretty_print_method out_channel (indent + 1))
    (function () -> do_indent out_channel indent)
    list
and pretty_print_method out_channel indent m =
  output_string out_channel ("op " ^ m.meth_name);
  if m.meth_inpars <> [] || m.meth_outpars <> [] then
    output_string out_channel "(";
  begin
    match (m.meth_inpars, m.meth_outpars) with
      ([], []) -> ()
    | (i, []) ->
	output_string out_channel "in ";
	pretty_print_vardecls out_channel 0 "" ", " "" i
    | ([], o) ->
	output_string out_channel "out ";
	pretty_print_vardecls out_channel 0 "" ", " "" o
    | (i, o) -> 
	output_string out_channel "in ";
	pretty_print_vardecls out_channel 0 "" ", " "" i;
	output_string out_channel "; out ";
	pretty_print_vardecls out_channel 0 "" ", " "" o
  end;
  if m.meth_inpars <> [] || m.meth_outpars <> [] then
    output_string out_channel ")";
  (match m.meth_body with
      None -> ()
    | Some s ->
	output_string out_channel " == " ;
	do_indent out_channel indent;
	separated_list
	  (function v ->
	    output_string out_channel "var " ;
	    pretty_print_vardecl out_channel v)
	  (function () ->
	    output_string out_channel ";" ;
	    do_indent out_channel indent)
	  m.meth_vars;
	if [] <> m.meth_vars then
	  begin
	    output_string out_channel ";" ;
	    do_indent out_channel indent
	  end ;
	pretty_print_statement out_channel indent s);
  output_string out_channel "\n"
and pretty_print_vardecls out_channel lvl p d s list =
  separated_list
    (function v ->
      output_string out_channel p;
      pretty_print_vardecl out_channel v)
    (function () ->
      output_string out_channel d;
      if lvl > 0 then do_indent out_channel lvl)
    list
and pretty_print_vardecl out_channel v =
  output_string out_channel (v.var_name ^ ": " ^ (Type.as_string v.var_type ));
  ( match v.var_init with
      Some e -> output_string out_channel " := " ;
	pretty_print_expression out_channel e
    | None -> () )
and pretty_print_statement out lvl statement =
  (** Pretty-print statements and write the code to out. *)
  let open_block prec op_prec =
    if prec < op_prec then output_string out "begin "
  and close_block prec op_prec =
    if prec < op_prec then output_string out " end"
  in
  let rec print lvl prec =
    function
	Skip _ -> output_string out "skip";
      | Assert (_, e) ->
	output_string out "assert " ; pretty_print_expression out e
      | Prove (_, e) ->
	output_string out "prove " ; pretty_print_expression out e
      | Assign (_, i, e) ->
	  pretty_print_identifier_list out i;
	  output_string out " := ";
	  pretty_print_expression_list out e;
      | Await (_, e) -> 
	  output_string out "await ";
	  pretty_print_expression out e;
      | AsyncCall (_, l, c, m, a) ->
	  (match l with
	      None -> ()
	    | Some l -> output_string out l ) ;
	  output_string out "!";
	  pretty_print_expression out c ;
	  output_string out ("." ^ m);
	  output_string out "(" ;
	  pretty_print_expression_list out a;
	  output_string out ")"
      | Reply (_, l, o) ->
	  output_string out (l ^ "?(");
	  pretty_print_identifier_list out o;
	  output_string out ")";
      | Free(_, l) -> output_string out ("/* free(" ^ l ^ ") */")
      | SyncCall (_, c, m, a, r) ->
	  pretty_print_expression out c ;
	  output_string out ("." ^ m);
	  output_string out "(" ;
	  pretty_print_expression_list out a;
	  output_string out "; " ;
	  pretty_print_identifier_list out r;
	  output_string out ")"
      | LocalAsyncCall (_, l, m, lb, ub, i) ->
	  output_string out (match l with None -> "!" | Some n -> (n ^ "!"));
	  output_string out m;
	  (match lb with None -> () | Some n -> output_string out ("@" ^ n));
	  (match ub with None -> () | Some n -> output_string out ("<<" ^ n));
	  output_string out "(" ;
	  pretty_print_expression_list out i;
	  output_string out ")"
      | LocalSyncCall (_, m, l, u, i, o) ->
	  output_string out m;
	  (match l with None -> () | Some n -> output_string out ("@" ^ n));
	  (match u with None -> () | Some n -> output_string out ("<<" ^ n));
	  output_string out "(" ;
	  pretty_print_expression_list out i;
	  output_string out "; " ;
	  pretty_print_identifier_list out o;
	  output_string out ")"
      | Tailcall (_, m, l, u, i) -> assert false
      | If (_, c, t, f) ->
	  output_string out "if ";
	  pretty_print_expression out c;
	  output_string out " then";
	  do_indent out (lvl + 1);
	  print (lvl + 1) 25 t;
	  do_indent out lvl;
	  output_string out "else";
	  do_indent out (lvl + 1);
	  print (lvl + 1) 25 f;
	  do_indent out lvl;
	  output_string out "fi"
      | While (_, c, None, b) ->
	  output_string out "while ";
	  pretty_print_expression out c;
	  output_string out " do ";
	  do_indent out (lvl + 1);
	  print (lvl + 1) 25 b;
	  output_string out " od";
	  do_indent out lvl
      | While (_, c, Some i, b) ->
	  output_string out "while ";
	  pretty_print_expression out c;
	  do_indent out lvl;
	  output_string out "inv ";
	  pretty_print_expression out i;
	  do_indent out lvl;
	  output_string out "do ";
	  do_indent out (lvl + 1);
	  print (lvl + 1) 25 b;
	  output_string out " od";
	  do_indent out lvl
      | Sequence (_, sl) -> 
	  let op_prec = 25 in
	  let nl = lvl + if prec < op_prec then 1 else 0 in
	    open_block prec op_prec;
	    separated_list (function s -> print nl op_prec s)
	      (function () -> output_string out ";" ; do_indent out nl) sl ;
	    close_block prec op_prec
      | Merge (_, l, r) ->
	  let op_prec = 29 in
	  let nl = lvl + if prec < op_prec then 1 else 0 in
	    open_block prec op_prec;
	    print nl op_prec l;
	    output_string out " |||";
	    do_indent out nl;
	    print nl op_prec r;
	    close_block prec op_prec
      | Choice (_, l, r) -> 
	  let op_prec = 27 in
	  let nl = lvl + if prec < op_prec then 1 else 0 in
	    open_block prec op_prec;
	    print nl op_prec l;
	    output_string out " [] ";
	    do_indent out nl;
	    print nl op_prec r;
	    close_block prec op_prec
  in
    print lvl 25 statement
and pretty_print_expression out_channel exp =
  let open_paren prec op_prec =
    if prec < op_prec then output_string out_channel "("
  and close_paren prec op_prec =
    if prec < op_prec then output_string out_channel ")"
  in
  let rec print prec =
    function
	Nil _ -> output_string out_channel "nil"
      | Null _ -> output_string out_channel "null"
      | Int (_, i) -> output_string out_channel (string_of_int i)
      | Float (_, f) -> output_string out_channel (string_of_float f)
      | Bool (_, b) -> output_string out_channel (string_of_bool b)
      | String (_, s) -> output_string out_channel ("\"" ^ s ^ "\"")
      | Id (_, i) -> output_string out_channel i
      | Unary (_, o, e) ->
	  output_string out_channel (string_of_unaryop o ^ " ");
	  print (prec_of_unaryop o) e
      | Binary(_, o, l, r) ->
	  let lp = fst (prec_of_binaryop o)
	  and rp = snd (prec_of_binaryop o)
	  in
      	    open_paren prec lp; print lp l;
	    output_string out_channel (" " ^ (string_of_binaryop o) ^ " ");
	    print rp r; close_paren prec rp
      | FuncCall (_, i, a) ->
	  output_string out_channel (i ^ "(");
	  pretty_print_expression_list out_channel a;
	  output_string out_channel ")";
      | FieldAccess(_, e, f) -> print 15 e; output_string out_channel ("`" ^ f)
      | Wait _ -> output_string out_channel "wait"
      | Label (_, l) -> output_string out_channel (l ^ "?")
      | New (_, t, a) ->
          output_string out_channel ("new " ^ (Type.as_string t) ^ "(");
	  pretty_print_expression_list out_channel a ;
	  output_string out_channel ")"
  in
    print 121 exp
and pretty_print_expression_list out_channel l =
  separated_list (pretty_print_expression out_channel)
    (function () -> output_string out_channel ", ") l
and pretty_print_identifier_list out_channel l =
  separated_list (output_string out_channel)
    (function () -> output_string out_channel ". ") l
and do_indent out lvl =
  output_string out ("\n" ^ (String.make (lvl * 2) ' '))





module Maude =
struct

  type options = {
    mutable modelchecker: bool;
    mutable red_init: bool;
    mutable main: string option;
  }

  (* Write a Creol program as a maude term. If the program is parsable
     but not semantically correct, this function will only produce
     garbage. *)

  let rec of_creol_expression out =
    function
	Nil _ -> output_string out "list(emp)"
      | Null _ -> output_string out "null"
      | Int (_, i) -> output_string out ("int(" ^ (string_of_int i) ^ ")")
      | Float (_, f) -> ()
      | Bool (_, false) -> output_string out "bool(false)"
      | Bool (_, true) -> output_string out "bool(true)"
      | String (_, s) -> output_string out ("str(\"" ^ s ^ "\")")
      | Id (_, i) -> output_string out ("\"" ^ i ^ "\"")
      | Unary (_, _, _) -> assert false
      | Binary (_, GuardAnd, l, r) -> output_string out "( " ;
	of_creol_expression out l ; output_string out " & " ;
	of_creol_expression out r ; output_string out " )"
      | Binary (_, _, _, _) -> assert false
      | FuncCall(_, f, a) -> output_string out ("\"" ^ f ^ "\" ( " );
	  of_creol_expression_list out a;
	  output_string out " )"
	    (* Queer, but parens are required for parsing Appl in ExprList. *)
      | FieldAccess(_, e, f) -> assert false (* XXX *)
      | Wait _ -> output_string out "wait"
      | Label(_, l) -> output_string out ("( \"" ^ l ^ "\" ?? )")
      | New (_, c, a) ->
	  output_string out ("new \"" ^ (match c with Type.Basic s -> s | Type.Application (s, _) -> s | _ -> assert false) ^ "\" ( ") ;
	  of_creol_expression_list out a ;
	  output_string out " )"
  and of_creol_expression_list out_channel =
    (** Compile a list of expressions into the Creol Maude Machine. *)
    function
	[] -> output_string out_channel "emp"
      | [e] -> of_creol_expression out_channel e
      | e::l -> of_creol_expression out_channel e;
	  output_string out_channel " # ";
	  of_creol_expression_list out_channel l
  and of_creol_identifier_list out_channel =
    (** Convert a list of identifiers into a list of Attribute identifiers. *)
    function
	[] -> output_string out_channel "noAid"
      | [i] -> output_string out_channel ("\"" ^ i ^ "\"")
      | i::l -> output_string out_channel ("\"" ^ i ^ "\", ");
	  of_creol_identifier_list out_channel l

  let of_creol_statement out stmt =
    let open_paren prec op_prec =
      if prec < op_prec then output_string out "( " ;
    and close_paren prec op_prec =
      if prec < op_prec then output_string out " )" ;
    in let rec print prec =
      function
	  Skip _ -> output_string out "skip"
	| Assert (_, _) -> output_string out "skip"
	| Prove (_, _) -> output_string out "skip"
	| Await (_, e) -> output_string out "( await ";
	    of_creol_expression out e;
	    output_string out " )"
	| Assign (_, i, e) ->
	    of_creol_identifier_list out i;
	    output_string out " ::= " ;
	    of_creol_expression_list out e
	| AsyncCall (_, l, c, m, a) ->
	    output_string out (match l with
		None -> "\"Dummy\""
	      | Some l ->  "\"" ^ l ^ "\"") ;
	    output_string out " ! ";
	    of_creol_expression out c ;
	    output_string out (" . \"" ^ m ^ "\" ( ") ;
	    of_creol_expression_list out a;
	    output_string out " )"
	| Reply (_, l, o) ->
	    output_string out ("( \"" ^ l ^ "\" ? ( ") ;
	    of_creol_identifier_list out o;
	    output_string out " ) ) "
	| Free (_, l) -> output_string out ("free( \"" ^ l ^ "\" )")
	| SyncCall (_, c, m, a, r) ->
	    of_creol_expression out c ;
	    output_string out (" . \"" ^ m ^ "\" ( ");
	    of_creol_expression_list out a;
	    output_string out " ; " ;
	    of_creol_identifier_list out r;
	    output_string out " )"
	| LocalAsyncCall (_, l, m, lb, ub, i) ->
	    output_string out
	      (match l with None -> "\"Dummy\" !" | Some n -> ("\"" ^ n ^ "\" !"));
	    output_string out ( " \"this\" . \"" ^ m ^ "\"");
	    (match lb with None -> () | Some n -> output_string out (" @ \"" ^ n ^ "\""));
	    (match ub with None -> () | Some n -> output_string out (" << \"" ^ n ^ "\""));
	    output_string out " ( " ;
	    of_creol_expression_list out i;
	    output_string out " )"
	| LocalSyncCall (_, m, l, u, i, o) ->
	    output_string out ( "\"" ^ m ^ "\"");
	    (match l with None -> () | Some n -> output_string out (" @ \"" ^ n ^ "\""));
	    (match u with None -> () | Some n -> output_string out (" << \"" ^ n ^ "\""));
	    output_string out " ( " ;
	    of_creol_expression_list out i;
	    output_string out " ; " ;
	    of_creol_identifier_list out o;
	    output_string out " )"
	| Tailcall (_, m, l, u, i) ->
	    output_string out ( "\"" ^ m ^ "\"");
	    (match l with None -> () | Some n -> output_string out (" @ \"" ^ n ^ "\""));
	    (match u with None -> () | Some n -> output_string out (" << \"" ^ n ^ "\""));
	    output_string out " ( " ;
	    of_creol_expression_list out i;
	    output_string out " )"
	| If (_, c, t, f) ->
	    output_string out "if "; of_creol_expression out c;
	    output_string out " th "; print 25 t;
	    output_string out " el "; print 25 f;
	    output_string out " fi"
	| While (_, c, _, b) ->
	    output_string out "while " ;
	    of_creol_expression out c;
	    output_string out " do ";
	    print 25 b;
	    output_string out " od "
	| Sequence (_, sl) ->
	    let op_prec = 25 in
	      open_paren prec op_prec ;
	      separated_list (function s -> print op_prec s)
		(function () -> output_string out " ; ") sl;
	      close_paren prec op_prec
	| Merge (_, l, r) ->
	    let op_prec = 29 in
	      open_paren prec op_prec ;
	      print op_prec l; 
	      output_string out " ||| ";
	      print op_prec r; 
	      close_paren prec op_prec
	| Choice (_, l, r) ->
	    let op_prec = 27 in
	      open_paren prec op_prec ;
	      print op_prec l; 
	      output_string out " [] ";
	      print op_prec r; 
	      close_paren prec op_prec
    in print 25 stmt


  let of_creol_attribute out a =
    output_string out ("(" ^ a.var_name ^ ": ");
    (match a.var_init with
	None -> output_string out "null"
      | Some e -> of_creol_expression out e);
    output_string out ")"

  let rec of_creol_attribute_list out =
    function
	[] ->  output_string out "none"
      | [a] -> of_creol_attribute out a
      | a::l -> of_creol_attribute out a; output_string out ", ";
	  of_creol_attribute_list out l

  let of_creol_inherits out =
    function
	(i, l) -> output_string out ("\"" ^ i ^ "\" < ");
	  of_creol_expression_list out l;
	  output_string out " > "

  let rec of_creol_inherits_list out =
    function
	[] -> output_string out "noInh"
      | [i] -> of_creol_inherits out i
      | i::r -> of_creol_inherits out i;
	  output_string out " ## ";
	  of_creol_inherits_list out r

  let rec of_creol_parameter_list out =
    function
	[] -> output_string out "noAid"
      | [v] -> output_string out ("\"" ^ v.var_name ^ "\"")
      | v::r -> output_string out ("\"" ^ v.var_name ^ "\" , ");
	  of_creol_parameter_list out r

  let rec of_creol_class_attribute_list out =
    function
	[] -> output_string out "noSubst" 
      | [v] -> output_string out ("\"" ^ v.var_name ^ "\" |-> null")
      | v::r -> output_string out ("\"" ^ v.var_name ^ "\" |-> null , ");
	  of_creol_class_attribute_list out r

  let rec of_creol_method_return out =
    function
	[] -> output_string out "emp" 
      | [n] -> output_string out ("\"" ^ n.var_name ^ "\"")
      | n::l -> output_string out ("\"" ^ n.var_name ^ "\" # ");
          of_creol_method_return out l

  let of_creol_method out m =
    output_string out ("\n  < \"" ^ m.meth_name ^ "\" : Mtdname | Param: ");
    of_creol_parameter_list out m.meth_inpars;
    output_string out ", Latt: " ;
    of_creol_class_attribute_list out
      (m.meth_inpars @ m.meth_outpars @ m.meth_vars);
    output_string out ", Code: " ;
    ( match m.meth_body with
	None -> output_string out "skip"
      | Some s -> of_creol_statement out s ;
	  output_string out " ; return ( ";
	  of_creol_method_return out m.meth_outpars;
	  output_string out " )" ) ;
    output_string out " >"

  let rec of_creol_method_list out =
    function
	[] -> output_string out "noMtd" 
      | [m] -> of_creol_method out m
      | m::r -> of_creol_method out m;
	  output_string out " *";
	  of_creol_method_list out r

  let of_creol_with_defs out ws =
    let methods = List.flatten (List.map (function w -> w.With.methods) ws) in
      of_creol_method_list out methods

  let of_creol_class out c =
    output_string out ("< \"" ^ c.Class.name ^ "\" : Cl | Inh: ");
    of_creol_inherits_list out c.Class.inherits;
    output_string out ", Par: ";
    of_creol_parameter_list out c.Class.parameters;
    output_string out ", Att: ";
    of_creol_class_attribute_list out
      (c.Class.parameters @ c.Class.attributes);
    output_string out ", Mtds: ";
    of_creol_with_defs out c.Class.with_defs;
    output_string out ", Ocnt: 0 >\n\n"

  let of_creol_interface out i = ()

  let of_exception out e = ()

  let of_datatype out d = ()

  let of_creol_declaration out =
    function
	Class c -> of_creol_class out c
      | Interface i -> of_creol_interface out i
      | Exception e -> of_exception out e
      | Datatype d -> of_datatype out d

  let rec of_creol_decl_list out =
    function
	[] -> output_string out "noConf\n"
      | [d] -> of_creol_declaration out d
      | d::l -> of_creol_declaration out d; of_creol_decl_list out l

  let of_creol options out l =
    (** Convert an abstract syntax tree l of a creol program to a
	representation for the Maude CMC and write the result to the
	output channel out. *)
    if options.modelchecker then
      output_string out "load modelchecker\n"
    else
      output_string out "load interpreter\n";
    output_string out
      ("mod PROGRAM is\npr " ^ (if options.modelchecker then
	"CREOL-MODEL-CHECKER" else "INTERPRETER") ^
	  " .\nop init : -> Configuration [ctor] .\neq init =\n") ;
    of_creol_decl_list out l ;
    begin
      match options.main with
	  None -> ()
	| Some m -> output_string out ("main( \"" ^ m ^ "\" , emp )\n")
    end ;
    output_string out ".\nendm\n" ;
    if options.modelchecker then
      begin
	output_string out "\n\nmod PROGRAM-CHECKER is\n  protecting MODEL-CHECKER .\n  protecting PROGRAM .\n  protecting CREOL-PREDICATES .\nendm\n"
      end;
    if options.red_init then output_string out "\nred init .\n" ;
    flush out

end
