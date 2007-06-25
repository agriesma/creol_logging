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
    type 'c t =
	Basic of 'c * string
	| Application of 'c * string * 'c t list
	| Variable of 'c * string
	| Label of 'c

    (* These are the support functions for the abstract syntax tree. *)

    let rec as_string =
      function
	  Basic (_, s) -> s
	| Application (_, s, p) ->
	    s ^ "[" ^ (string_of_creol_type_list p) ^ "]"
	| Variable (_, s) -> "$" ^ s
	| Label _ -> "/* Label */"
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
    
    type ('b, 'c) t =
	Null of 'b
	| Nil of 'b
	| Bool of 'b * bool
	| Int of 'b * int
	| Float of 'b * float
	| String of 'b * string
	| Id of 'b * string
        | StaticAttr of 'b * string * 'c Type.t
	| Tuple of 'b * ('b, 'c) t list
	| Cast of 'b * ('b, 'c) t * 'c Type.t
	| Index of 'b * ('b, 'c) t * ('b, 'c) t
        | FieldAccess of 'b * ('b, 'c) t * string
	| Unary of 'b * unaryop * ('b, 'c) t
	| Binary of 'b * binaryop * ('b, 'c) t * ('b, 'c) t
	| If of 'b * ('b, 'c) t * ('b, 'c) t * ('b, 'c) t
	| Case of 'b * (('b, 'c) t, unit, ('b, 'c) t, ('b, 'c) t) Case.t
	| Typecase of 'b * (('b, 'c) t, 'c Type.t, ('b, 'c) t, ('b, 'c) t) Case.t
	| FuncCall of 'b * string * ('b, 'c) t list
	| Label of 'b * string
	| New of 'b * 'c Type.t * ('b, 'c) t list
  and ('b, 'c) lhs =
      LhsVar of 'b * string
    | LhsAttr of 'b * string * 'c Type.t
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
	| Prepend
	| Append
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
	| Modulo -> "%"
	| Eq -> "="
	| Ne -> "/="
	| Le -> "<="
	| Lt -> "<"
	| Ge -> ">="
	| Gt -> ">"
	| And -> "&&"
	| Or -> "||"
	| Xor -> "^"
	| Implies -> "=>"
	| Iff -> "<=>"
	| Prepend -> "-|"
	| Append -> "|-"
	| Concat -> "|-|"
	| Project -> "\\"
	| GuardAnd -> "&"
	| In -> "in"

    let prec_of_binaryop =
      function
	  Plus -> (33, 33)
	| Minus -> (33, 33)
	| Times -> (31, 31)
	| Div -> (31, 31)
	| Modulo -> (31, 31)
	| Eq -> (51, 51)
	| Ne -> (51, 51)
	| Le -> (37, 37)
	| Lt -> (37, 37)
	| Ge -> (37, 37)
	| Gt -> (37, 37)
	| In -> (53, 53)
	| And -> (55, 55)
	| Or -> (59, 59)
	| Xor -> (57, 57)
	| Implies -> (61, 61)
	| Iff -> (61, 61)
	| Prepend -> (33, 33)
	| Append -> (33, 33)
	| Concat -> (33, 33)
	| Project -> (35, 35)
	| GuardAnd -> (61, 61)

    let string_of_unaryop =
      function
	  Not -> "~"
	| UMinus -> "-"
	| Length -> "#"

    let prec_of_unaryop =
      function
	  Not -> 53
	| UMinus -> 15
	| Length -> 15

    let note =
      function
	  Null a -> a
	| Nil a -> a
	| Bool (a, _) -> a
	| Int (a, _) -> a
	| Float (a, _) -> a
	| String (a, _) -> a
	| Id (a, _) -> a
	| StaticAttr(a, _, _) -> a
	| Tuple (a, _) -> a
	| Cast (a, _, _) -> a
	| Index (a, _, _) -> a
	| FieldAccess (a, _, _) -> a
	| Unary (a, _, _) -> a
	| Binary (a, _, _, _) -> a
	| If (a, _, _, _) -> a
	| Case (a, _) -> a
	| Typecase (a, _) -> a
	| FuncCall (a, _, _) -> a
	| Label (a, _) -> a
	| New (a, _, _) -> a

    let name =
      function
	  LhsVar(_, n) -> n
	| LhsAttr(_, n, _) -> n
  end

open Expression

module Statement =
  struct
    type ('a, 'b, 'c) t =
	Skip of 'a
	| Release of 'a
	| Assert of 'a * ('b, 'c) Expression.t
	| Assign of 'a * ('b, 'c) Expression.lhs list * ('b, 'c) Expression.t list
	| Await of 'a * ('b, 'c) Expression.t
	| AsyncCall of 'a * string option * ('b, 'c) Expression.t * string *
	    ('b, 'c) Expression.t list
	| Reply of 'a * string * ('b, 'c) Expression.lhs list
	| Free of 'a * string
	| SyncCall of 'a * ('b, 'c) Expression.t * string *
	    ('b, 'c) Expression.t list * ('b, 'c) Expression.lhs list
	| AwaitSyncCall of 'a * ('b, 'c) Expression.t * string *
	    ('b, 'c) Expression.t list * ('b, 'c) Expression.lhs list
	| LocalAsyncCall of 'a * string option * string * string option *
	    string option * ('b, 'c) Expression.t list
	| LocalSyncCall of 'a * string * string option * string option *
            ('b, 'c) Expression.t list * ('b, 'c) Expression.lhs list
	| AwaitLocalSyncCall of 'a * string * string option * string option *
            ('b, 'c) Expression.t list * ('b, 'c) Expression.lhs list
	| Tailcall of 'a * string * string option * string option *
	    ('b, 'c) Expression.t list
	| If of 'a * ('b, 'c) Expression.t * ('a, 'b, 'c) t * ('a, 'b, 'c) t
	| While of 'a * ('b, 'c) Expression.t * ('b, 'c) Expression.t option * ('a, 'b, 'c) t
	| For of 'a * string * ('b, 'c) Expression.t * ('b, 'c) Expression.t *
	    ('b, 'c) Expression.t option * ('b, 'c) Expression.t option * ('a, 'b, 'c) t
	| Raise of 'a * string * ('b, 'c) Expression.t list
	| Try of 'a * ('a, 'b, 'c) t * ('a, 'b, 'c) catcher list
        | Case of 'a *
	    (('b, 'c) Expression.t, unit, ('b, 'c) Expression.t, ('a, 'b, 'c) t) Case.t
	| Typecase of 'a *
	    (('b, 'c) Expression.t, 'c Type.t, ('b, 'c) Expression.t, ('a, 'b, 'c) t) Case.t
	| Sequence of 'a * ('a, 'b, 'c) t  * ('a, 'b, 'c) t
	| Merge of 'a * ('a, 'b, 'c) t * ('a, 'b, 'c) t
	| Choice of 'a * ('a, 'b, 'c) t * ('a, 'b, 'c) t
        | Extern of 'a * string
    and ('a, 'b, 'c) catcher =
	{ catch: string option;
	  catch_parameters: string list;
	  catch_statement: ('a, 'b, 'c) t }
    and ('a, 'b, 'c) typecase =
	{ with_type: 'c Type.t option; with_statement: ('a, 'b, 'c) t }

    let note =
      function
	  Skip a -> a
	| Assert (a, _) -> a
	| Assign (a, _, _) -> a
	| Release a -> a
	| Await (a, _) -> a
	| AsyncCall (a, _, _, _, _) -> a
	| Reply (a, _, _) -> a
	| Free (a, _) -> a
	| SyncCall (a, _, _, _, _) -> a
	| AwaitSyncCall (a, _, _, _, _) -> a
	| LocalAsyncCall (a, _, _, _, _, _) -> a
	| LocalSyncCall (a, _, _, _, _, _) -> a
	| AwaitLocalSyncCall (a, _, _, _, _, _) -> a
	| Raise (a, _, _) -> a
	| Extern(a, _) -> a
	| Tailcall (a, _, _, _, _) -> a
	| If (a, _, _, _) -> a
	| While (a, _, _, _) -> a
	| For (a, _, _, _, _, _, _) -> a
	| Try (a, _, _) -> a
	| Case (a, _) -> a
	| Typecase (a, _) -> a
	| Sequence(a, _, _) -> a
	| Merge(a, _, _) -> a
	| Choice(a, _, _) -> a

    let is_skip =
      (** Test, whether the statement is a skip statement. *)
      function
	Skip _ -> true
	| _ -> false

    let rec normalize_sequences stmt =
      (** Transform an arbitrary statement [stmt] into a statement in
	  which all sequences are right-threaded, i.e., the first (or
	  left) part of a sequence statement is always a non-sequence
	  statement. *)
      let rec append_to_sequence stm1 stm2 =
	(** Append the sequence of statement [stm2] to the sequence
	    [stm1].  Assumes that both statement sequences are
	    right-threaded. *)
	match stm1 with
	    Sequence(a, s1, s2) ->
	      Sequence(a, s1, append_to_sequence s2  stm2)
	  | _ -> Sequence (note stm1, stm1, stm2)
      in
	match stmt with
	    If (a, c, s1, s2) ->
	      If (a, c, normalize_sequences s1, normalize_sequences s2)
	  | While (a, c, i, s) -> 
	      While (a, c, i, normalize_sequences s)
	  | For (a, v, st, en, sr, i, s) ->
	      For (a, v, st, en, sr, i, normalize_sequences s)
	  | Try (a, _, _) -> assert false (* XXX *)
	  | Case _ -> assert false (* XXX *)
	  | Typecase _ -> assert false (* XXX *)
	  | Sequence (a, (Sequence _ as s1), (Sequence _ as s2)) ->
	      append_to_sequence (normalize_sequences s1)
		(normalize_sequences s2)
	  | Sequence (a, Sequence (a1, s11, s12), s2) ->
	      Sequence (a, s11, normalize_sequences (Sequence (a1, s12, s2)))
	  | Sequence (a, s1, (Sequence _ as s2)) ->
	      Sequence (a, s1, normalize_sequences s2)
	  | Merge (a, s1, s2) ->
	      Merge (a, normalize_sequences s1, normalize_sequences s2)
	  | Choice (a, s1, s2) ->
	      Choice (a, normalize_sequences s1, normalize_sequences s2)
	  | _ -> stmt

  end

open Statement

(** The abstract syntax of Creol *)
type ('b, 'c) creol_vardecl =
    { var_name: string; var_type: 'c Type.t; var_init: ('b, 'c) Expression.t option }

type ('a, 'b, 'c) creolmethod =
    { meth_name: string;
      meth_inpars: ('b, 'c) creol_vardecl list;
      meth_outpars: ('b, 'c) creol_vardecl list;
      meth_vars: ('b, 'c) creol_vardecl list;
      meth_body: ('a, 'b, 'c) Statement.t option }





module With = struct

  type ('a, 'b, 'c) t = {
    co_interface: string option;
    methods: ('a, 'b, 'c) creolmethod list;
    invariants: ('b, 'c) Expression.t list
  }

end





module Class =
struct

  type ('b, 'c) inherits = string * (('b, 'c) Expression.t list)

  type ('a, 'b, 'c) t =
      { name: string;
	parameters: ('b, 'c) creol_vardecl list;
	inherits: ('b, 'c) inherits list;
	contracts: string list;
	implements: string list;
	attributes: ('b, 'c) creol_vardecl list;
	with_defs: ('a, 'b, 'c) With.t list }

end





module Interface =
struct

  type  ('a, 'b, 'c) t =
      { name: string;
	inherits: string list;
	with_decl: ('a, 'b, 'c) With.t option }

end

module Exception =
struct
  type ('b, 'c) t = { name: string; parameters: ('b, 'c) creol_vardecl list }
end





module Datatype =
struct

  type ('a, 'b, 'c) t = {
    name: string
  }

end





module Declaration =
struct

  type ('a, 'b, 'c) t =
      Class of ('a, 'b, 'c) Class.t
      | Interface of ('a, 'b, 'c) Interface.t
      | Datatype of ('a, 'b, 'c) Datatype.t
      | Exception of ('b, 'c) Exception.t

end

open Declaration




(** A counter used to generate the next fresh label *)
let next_fresh_label = ref 0

let fresh_label () =
  (* make a fresh label *)
  let res = "sync." ^ (string_of_int !next_fresh_label) in
    next_fresh_label := !next_fresh_label + 1 ; res


let lower ~input ~copy_stmt_note ~expr_note_of_stmt_note ~copy_expr_note =
  (** Normalise an abstract syntax tree by replacing all derived concepts
      with there basic equivalents *)
  let rec lower_expression =
    function
	Unary(a, o, e) ->
	  (* Do not copy the note, since the content should be invariant. *)
	  FuncCall(a, string_of_unaryop o, [lower_expression e])
      | Binary(a, o, l, r) ->
	  (* Do not copy the note, since the content should be invariant. *)
	  FuncCall(a, string_of_binaryop o, [lower_expression l;
					     lower_expression r])
      | FuncCall(a, f, args) -> FuncCall(a, f, List.map lower_expression args)
      | New (a, t, p) -> New (a, t, List.map lower_expression p)
      | t -> t
  and lower_expression_option =
    function
	None -> None
      | Some expr -> Some (lower_expression expr)
  and lower_guard note guard =
    let rec sort_guard =
      function
	  Binary(_, _, Label(_, _), Label (_, _)) as g -> g
	| Binary(a, o, left, Label (b, l)) ->
	    Binary (a, o, Label (b, l), sort_guard left)
	| g -> g
    and split_guard note =
      function
	  Binary(a, (GuardAnd | And), Label(ll, l), e) ->
            Sequence(note, Await (note, Label (ll, l)), split_guard note e)
	| Binary(a, Or, Label(ll, l), e) ->
            Choice(note, Await (note, Label (ll, l)), split_guard note e)
	| e -> Await (note, lower_expression e)
    in
      split_guard note (sort_guard guard)
  and lower_statement =
    function
	Skip _ as s -> s
      | Release _ as s -> s
      | Assert (a, e) -> Assert (a, lower_expression e)
      | Assign (a, s, e) -> Assign (a, s, List.map lower_expression e)
      | Await (note, g) -> lower_guard note g
      | AsyncCall (a, None, e, n, p) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  Sequence (a, AsyncCall (copy_stmt_note a,
				 Some ".anon", lower_expression e, n,
				 List.map lower_expression p),
		   Free (copy_stmt_note a, ".anon"))
      | AsyncCall (a, Some l, e, n, p) ->
	  AsyncCall (a, Some l, lower_expression e, n,
		    List.map lower_expression p)
      | Free _ as s -> s
      | Reply _ as s -> s
      | SyncCall (a, e, n, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
          let ne = lower_expression e
	  and np = List.map lower_expression p
	  and l = fresh_label ()
          in
	    Sequence (a, AsyncCall (copy_stmt_note a,
				   Some l, ne, n, np),
		     Reply (copy_stmt_note a, l, r))
      | AwaitSyncCall (a, e, n, p, r) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
          let ne = lower_expression e
	  and np = List.map lower_expression p
	  and l = fresh_label ()
          in
	    Sequence (a, AsyncCall (copy_stmt_note a, Some l, ne, n, np),
		     Sequence(copy_stmt_note a,
			     Await (copy_stmt_note a, Label(Expression.note ne, l)),
			     Reply (copy_stmt_note a, l, r)))
      | LocalAsyncCall (a, None, m, lb, ub, i) ->
	  (* If a label name is not given, we assign a new one and free it
	     afterwards.  It may be better to insert free later, but for this
	     we need smarter semantic analysis. *)
	  Sequence (a, LocalAsyncCall(copy_stmt_note a, Some ".anon", m, lb, ub,
				     List.map lower_expression i),
		   Free (copy_stmt_note a, ".anon"))
      | LocalAsyncCall (a, Some l, m, lb, ub, i) ->
	  LocalAsyncCall (a, Some l, m, lb, ub, List.map lower_expression i)
      | LocalSyncCall (a, m, l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
	  let ni = List.map lower_expression i
	  and lab = fresh_label ()
          in
	    Sequence (a, LocalAsyncCall (copy_stmt_note a, Some lab, m, l, u, ni),
		     Reply (copy_stmt_note a, lab, o))
      | AwaitLocalSyncCall (a, m, l, u, i, o) ->
	  (* Replace the synchronous call by the sequence of an asynchronous
	     call followed by a reply.  This generates a fresh label name.
	     
	     XXX: Usually, we nest a sequence into a sequence here, which is
	     not very nice.  May be we want to have something smarter for
	     sequences which avoids this nesting? *)
	  let ni = List.map lower_expression i
	  and lab = fresh_label ()
          in
	    Sequence (a, LocalAsyncCall (copy_stmt_note a, Some lab, m, l, u, ni),
		     Sequence (copy_stmt_note a, Await (copy_stmt_note a,
						       Label(expr_note_of_stmt_note a, lab)),
			      Reply (copy_stmt_note a, lab, o)))
      | Tailcall (a, m, l, u, i) ->
	  Tailcall (a, m, l, u, List.map lower_expression i)
      | If (a, c, t, f) -> If(a, lower_expression c, lower_statement t,
			     lower_statement f)
      | While (a, c, None, b) ->
	  While (a, lower_expression c, None, lower_statement b)
      | While (a, c, Some i, b) ->
	  While (a, lower_expression c, Some (lower_expression i),
		lower_statement b)
      | For (a, i, first, last, stride, inv, body) ->
	  For (a, i, lower_expression first, lower_expression last,
	      lower_expression_option stride,
	      lower_expression_option inv,
	      lower_statement body)
      | Raise _ -> assert false
      | Try _ -> assert false
      | Case _ -> assert false
      | Typecase _ -> assert false
      | Sequence (a, s1, s2) ->
	  let ls1 = lower_statement s1
	  and ls2 = lower_statement s2 in
	    Sequence (a, ls1, ls2)
      | Merge (a, s1, s2) -> Merge (a, lower_statement s1,
				   lower_statement s2)
      | Choice (a, s1, s2) -> Choice (a, lower_statement s1,
				     lower_statement s2)
      | Extern _ as s -> s
  and lower_method_variables note vars =
    (** Compute a pair of a new list of local variable declarations
	and a list of assignments used for initialisation.

	if the variable list is empty or no variable in the list has an
	initializer, this function will produce a skip statement as the
	method-call's initialization.  The caller of this function should
	check for this and discard the initalization block.

	The initialisation component of variable declarations will be
	removed. *)
    let lower_method_variable =
      function 
          ({ var_name = n ; var_type = _ ; var_init = Some i } as v) ->
	    ([{ v with var_init = None }],
	    Assign(note, [LhsVar(Expression.note i, n)], [lower_expression i]))
        | v -> ([v], Skip note)
    in
      match vars with
	  [] -> ([], Skip note)
	| [v] -> (lower_method_variable v)
	| v::l ->
	    let vl = lower_method_variable v
	    and ll = lower_method_variables note l in
	      match vl with
		  (vll, Assign _) -> (vll@(fst ll), Sequence(note, (snd vl), (snd ll)))
		| (vll, Skip _) -> (vll@(fst ll), (snd ll))
		| _ -> assert false
  and lower_method m =
    (** Simplify a method definition. *)
    let _ = next_fresh_label := 0 (* Labels must only be unique per method. *)
    in
    match m.meth_body with
	None -> m
      | Some mb  ->
	  let smv = lower_method_variables (Statement.note mb) m.meth_vars in
	    { m with meth_vars = fst smv ;
	      meth_body = Some( if Statement.is_skip (snd smv) then
		lower_statement mb
		else
		  Sequence(Statement.note mb, snd smv,
			  lower_statement mb)) }
  and lower_with w =
    { w with With.methods = List.map lower_method w.With.methods }
  and lower_inherits =
    function
	(n, e) -> (n, List.map lower_expression e)
  and lower_inherits_list =
    function
	[] -> []
      | i::l -> (lower_inherits i)::(lower_inherits_list l)
  and lower_class c =
    { c with Class.inherits = lower_inherits_list c.Class.inherits;
      Class.with_defs = List.map lower_with c.Class.with_defs }
  and lower_interface i =
    i
  and lower_declaration =
    function
	Class c -> Class (lower_class c)
      | Interface i -> Interface (lower_interface i)
      | Exception e -> Exception e
      | Datatype d -> Datatype d
  in
    List.map lower_declaration input

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
      | Assign (n, lhs, rhs) ->
	  Assign ({n with Note.env = note.Note.env }, lhs, rhs)
	(* XXX: Completely broken...
	  Assign ({ n with Note.env = 
	      List.fold_left (fun e n -> define e n false)
		note.Note.env (name lhs)}, lhs, rhs) *)
      | Await (n, g) ->
	  Await ({ n with Note.env = note.Note.env }, g)
      | Release a ->
	  Release { a with Note.env = note.Note.env }
      | AsyncCall (n, None, c, m, a) ->
	  (* XXX: This should not happen, but if we resolve this, we need to
	     rerun this for updating the chain... *)
	  AsyncCall ({ n with Note.env = note.Note.env }, None, c, m, a)
      | AsyncCall (n, Some l, c, m, a) ->
	  AsyncCall ({ n with Note.env = (define note.Note.env l true) },
		    Some l, c, m, a)
      | Reply (n, l, p) ->
	  Reply ({ n with Note.env = note.Note.env } , l, p)
      | Free (n, v) -> assert false
      | SyncCall (n, c, m, ins, outs) ->
	  SyncCall ({ n with Note.env = note.Note.env }, c, m, ins, outs) (* XXX *)
      | AwaitSyncCall (n, c, m, ins, outs) ->
	  AwaitSyncCall ({ n with Note.env = note.Note.env }, c, m, ins, outs) (* XXX *)
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
      | AwaitLocalSyncCall (n, m, u, l, a, r) ->
	  AwaitLocalSyncCall ({ n with Note.env = note.Note.env },
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
      | For _ -> assert false
      | Raise _ -> assert false
      | Try _ -> assert false
      | Case _ -> assert false
      | Typecase _ -> assert false
      | Sequence (n, s1, s2) ->
	  let ns1 = (definitions_in_statement note s1) in
	  let ns2 = (definitions_in_statement note s2) in
	    Sequence ({n with Note.env = Note.join (Statement.note ns1).Note.env
		(Statement.note ns2).Note.env},
		  ns1, ns2)
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
      | Extern (n, s) -> Extern (n, s)

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
    | Assign (a, l, r) -> assert false
    | Await (a, g) -> assert false
    | Release a -> assert false
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
    | For _ -> assert false
    | Raise _ -> assert false
    | Try _ -> assert false
    | Case _ -> assert false
    | Typecase _ -> assert false
    | Sequence (a, s1, s2) ->
	let ns1 = uses_in_statement s1
	and ns2 = uses_in_statement s2 in
	  Sequence ({ a with
	    Note.env = Note.meet (Statement.note ns1).Note.env
	      (Statement.note ns2).Note.env },
		ns1, ns2)
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
      | Extern (n, s) -> Extern (n, s)
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
  and optimise_in_statement outs s = s
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

let pretty_print out_channel input =
  let rec pretty_print_declaration =
    function
	Class c -> pretty_print_class c
      | Interface i -> pretty_print_iface i
      | Exception e -> pretty_print_exception e
      | Datatype d -> pretty_print_datatype d
  and pretty_print_datatype d =
    output_string out_channel ("datatype " ^ d.Datatype.name ^ "\n");
    output_string out_channel "begin\n" ;
    output_string out_channel "end\n"
  and pretty_print_exception e =
    output_string out_channel ("exception " ^ e.Exception.name) ;
    begin
      match e.Exception.parameters with
          [] -> ()
	| l -> output_string out_channel "(";
	    pretty_print_vardecls 0 "" ", " "" l;
	    output_string out_channel ")" 
    end ;
    output_string out_channel "\n"
  and pretty_print_iface i =
    output_string out_channel "interface ";
    output_string out_channel i.Interface.name;
    output_string out_channel "\nbegin\n";  
    output_string out_channel "end"
  and pretty_print_class c =
    output_string out_channel ("class " ^ c.Class.name ^ " ") ;
    ( match c.Class.parameters with
	[] -> ()
      | l -> output_string out_channel "(";
	  pretty_print_vardecls 0 "" ", " "" l;
	  output_string out_channel ")" ) ;
    ( match c.Class.inherits with
	[] -> ()
      | l -> output_string out_channel "\ninherits ";
	  separated_list pretty_print_inherits
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
    do_indent 0;
    output_string out_channel "begin";
    if [] <> c.Class.attributes then
      begin
	do_indent 1 ;
	pretty_print_vardecls 1 "var " "" "\n" c.Class.attributes;
	output_string out_channel "\n";
      end;
    if [] <> c.Class.with_defs then
      begin
	List.iter (pretty_print_with) c.Class.with_defs ;
      end ;
    if [] = c.Class.attributes && [] = c.Class.with_defs then
      output_string out_channel "\n";
    output_string out_channel "end"
  and pretty_print_inherits (inh, args) =
    output_string out_channel inh;
    if args <> [] then
      begin
	output_string out_channel "(";
	separated_list pretty_print_expression
	  (function () -> output_string out_channel ", ") args;
	output_string out_channel ")"
      end
  and pretty_print_with w =
    let indent = if w.With.co_interface = None then 1 else 2
    in
      begin
	match w.With.co_interface with
	    None -> ()
	  | Some c ->
	      do_indent 1;
	      output_string out_channel ("with " ^ c);
      end ;
      do_indent indent;
      pretty_print_methods indent w.With.methods
	(* XXX: Take care of invariants later *)
  and pretty_print_methods indent list =
    separated_list
      (pretty_print_method (indent + 1))
      (function () -> do_indent indent)
      list
  and pretty_print_method indent m =
    output_string out_channel ("op " ^ m.meth_name);
    if m.meth_inpars <> [] || m.meth_outpars <> [] then
      output_string out_channel "(";
    begin
      match (m.meth_inpars, m.meth_outpars) with
	  ([], []) -> ()
	| (i, []) ->
	    output_string out_channel "in ";
	    pretty_print_vardecls 0 "" ", " "" i
	| ([], o) ->
	    output_string out_channel "out ";
	    pretty_print_vardecls 0 "" ", " "" o
	| (i, o) -> 
	    output_string out_channel "in ";
	    pretty_print_vardecls 0 "" ", " "" i;
	    output_string out_channel "; out ";
	    pretty_print_vardecls 0 "" ", " "" o
    end;
    if m.meth_inpars <> [] || m.meth_outpars <> [] then
      output_string out_channel ")";
    (match m.meth_body with
	None -> ()
      | Some s ->
	  output_string out_channel " == " ;
	  do_indent indent;
	  separated_list
	    (function v ->
	      output_string out_channel "var " ;
	      pretty_print_vardecl v)
	    (function () ->
	      output_string out_channel ";" ;
	      do_indent indent)
	    m.meth_vars;
	  if [] <> m.meth_vars then
	    begin
	      output_string out_channel ";" ;
	      do_indent indent
	    end ;
	  pretty_print_statement indent s);
    output_string out_channel "\n"
  and pretty_print_vardecls lvl p d s list =
    separated_list
      (function v ->
	output_string out_channel p;
	pretty_print_vardecl v)
      (function () ->
	output_string out_channel d;
	if lvl > 0 then do_indent lvl)
      list
  and pretty_print_vardecl v =
    output_string out_channel (v.var_name ^ ": " ^ (Type.as_string v.var_type ));
    ( match v.var_init with
	Some e -> output_string out_channel " := " ;
	  pretty_print_expression e
      | None -> () )
  and pretty_print_statement lvl statement =
    (** Pretty-print statements and write the code to out. *)
    let open_block prec op_prec =
      if prec < op_prec then output_string out_channel "begin "
    and close_block prec op_prec =
      if prec < op_prec then output_string out_channel " end"
    in
    let rec print lvl prec =
      function
	  Skip _ -> output_string out_channel "skip";
	| Assert (_, e) ->
	    output_string out_channel "assert " ; pretty_print_expression e
	| Assign (_, i, e) ->
	    pretty_print_lhs_list i;
	    output_string out_channel " := ";
	    pretty_print_expression_list e
	| Await (_, e) -> 
	    output_string out_channel "await ";
	    pretty_print_expression e;
	| Release _ -> output_string out_channel "release";
	| AsyncCall (_, l, c, m, a) ->
	    (match l with
		None -> ()
	      | Some l -> output_string out_channel l ) ;
	    output_string out_channel "!";
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel ")"
	| Reply (_, l, o) ->
	    output_string out_channel (l ^ "?(");
	    pretty_print_lhs_list o;
	    output_string out_channel ")";
	| Free(_, l) -> output_string out_channel ("/* free(" ^ l ^ ") */")
	| SyncCall (_, c, m, a, r) ->
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list r;
	    output_string out_channel ")"
	| AwaitSyncCall (_, c, m, a, r) ->
	    output_string out_channel "await " ;
	    pretty_print_expression c ;
	    output_string out_channel ("." ^ m ^ "(");
	    pretty_print_expression_list a;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list r;
	    output_string out_channel ")"
	| LocalAsyncCall (_, l, m, lb, ub, i) ->
	    output_string out_channel
	      (match l with
		  None -> "!"
		| Some n -> (n ^ "!"));
	    output_string out_channel m;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel ")"
	| LocalSyncCall (_, m, lb, ub, i, o) ->
	    output_string out_channel m;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list o;
	    output_string out_channel ")"
	| AwaitLocalSyncCall (_, m, lb, ub, i, o) ->
	    output_string out_channel ("await " ^ m) ;
	    (match lb with
		None -> ()
	      | Some n -> output_string out_channel (":>" ^ n));
	    (match ub with
		None -> ()
	      | Some n -> output_string out_channel ("<:" ^ n));
	    output_string out_channel "(" ;
	    pretty_print_expression_list i;
	    output_string out_channel "; " ;
	    pretty_print_lhs_list o;
	    output_string out_channel ")"
	| Tailcall (_, m, l, u, i) -> assert false
	| If (_, c, t, f) ->
	    output_string out_channel "if ";
	    pretty_print_expression c;
	    output_string out_channel " then";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 t;
	    do_indent lvl;
	    output_string out_channel "else";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 f;
	    do_indent lvl;
	    output_string out_channel "end"
	| While (_, c, i, b) ->
	    (* The text generated in this branch does not parse in standard
	       Creol.  This should not be changed.  Consult the manual for
	       the reasons. *)
	    output_string out_channel "while ";
	    pretty_print_expression c;
	    (match i with
		None -> ()
	      | Some inv -> 
		  do_indent lvl;
		  output_string out_channel "inv ";
		  pretty_print_expression inv ;
		  do_indent lvl) ;
	    output_string out_channel " do ";
	    do_indent (lvl + 1);
	    print (lvl + 1) 25 b;
	    output_string out_channel " od";
	    do_indent lvl
	| For _ -> assert false
	| Raise _ -> assert false
	| Try _ -> assert false
	| Case _ -> assert false
	| Typecase _ -> assert false
	| Sequence (_, s1, s2) -> 
	    let op_prec = 25 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec s1;
	      output_string out_channel "; ";
	      do_indent nl;
	      print nl op_prec s2;
	      close_block prec op_prec
	| Merge (_, l, r) ->
	    let op_prec = 29 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec l;
	      output_string out_channel " ||| ";
	      do_indent nl;
	      print nl op_prec r;
	      close_block prec op_prec
	| Choice (_, l, r) -> 
	    let op_prec = 27 in
	    let nl = lvl + if prec < op_prec then 1 else 0 in
	      open_block prec op_prec;
	      print nl op_prec l;
	      output_string out_channel " [] ";
	      do_indent nl;
	      print nl op_prec r;
	      close_block prec op_prec
    in
      print lvl 25 statement
  and pretty_print_expression exp =
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
	| StaticAttr (_, a, c) ->
	    output_string out_channel (a ^ "@" ^ (Type.as_string c))
	| Tuple (_, a) ->
	    output_string out_channel "(";
	    pretty_print_expression_list a;
	    output_string out_channel ")";
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
	    pretty_print_expression_list a;
	    output_string out_channel ")";
	| FieldAccess(_, e, f) -> print 15 e; output_string out_channel ("`" ^ f)
	| Label (_, l) -> output_string out_channel (l ^ "?")
	| New (_, t, a) ->
            output_string out_channel ("new " ^ (Type.as_string t) ^ "(");
	    pretty_print_expression_list a ;
	    output_string out_channel ")"
    in
      print 121 exp
  and pretty_print_expression_list l =
    separated_list pretty_print_expression
      (function () -> output_string out_channel ", ") l
  and pretty_print_lhs_list l =
    separated_list
      (function LhsVar (_, n) -> output_string out_channel n
	| LhsAttr(_, n, c) -> output_string out_channel
	    (n ^ "@" ^ (Type.as_string c)))
      (function () -> output_string out_channel ", ") l
  and pretty_print_identifier_list l =
    separated_list (output_string out_channel)
      (function () -> output_string out_channel ", ") l
  and do_indent lvl =
    output_string out_channel ("\n" ^ (String.make (lvl * 2) ' '))
  in
    separated_list pretty_print_declaration
      (function () -> output_string out_channel "\n\n") input ;
    output_string out_channel "\n";
    flush out_channel





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

  let of_creol ~options ~out_channel ~input =
    let rec of_type =
      function
	  Type.Basic (_, n) -> output_string out_channel n
	| Type.Application (_, n, _) -> output_string out_channel n
	| _ -> assert false
    and of_expression =
      function
	  Nil _ -> output_string out_channel "list(emp)"
	| Null _ -> output_string out_channel "null"
	| Int (_, i) -> output_string out_channel ("int(" ^ (string_of_int i) ^ ")")
	| Float (_, f) -> assert false
	| Bool (_, false) -> output_string out_channel "bool(false)"
	| Bool (_, true) -> output_string out_channel "bool(true)"
	| String (_, s) -> output_string out_channel ("str(\"" ^ s ^ "\")")
	| Id (_, i) -> output_string out_channel ("\"" ^ i ^ "\"")
	| StaticAttr(_, a, c) ->
	    output_string out_channel ("( \"" ^ a ^ "\" @@ \"");
	    of_type c ;
	    output_string out_channel "\" )"
	| FuncCall(_, f, a) -> output_string out_channel ("\"" ^ f ^ "\" ( " );
	    of_expression_list a;
	    output_string out_channel " )"
	      (* Queer, but parens are required for parsing Appl in ExprList. *)
	| FieldAccess(_, e, f) -> assert false (* XXX *)
	| Unary _ -> assert false
	| Binary _ -> assert false
	| Label(_, l) -> output_string out_channel ("( \"" ^ l ^ "\" ?? )")
	| New (_, c, a) ->
	    output_string out_channel
	      ("new \"" ^ (Type.as_string c) ^ "\" ( ") ;
	    of_expression_list a ;
	    output_string out_channel " )"
    and of_expression_list =
      (** Compile a list of expressions into the Creol Maude Machine. *)
      function
	  [] -> output_string out_channel "emp"
	| [e] -> of_expression e
	| e::l -> of_expression e;
	    output_string out_channel " # ";
	    of_expression_list l
    and of_identifier_list =
      (** Convert a list of identifiers into a list of Attribute identifiers. *)
      function
	  [] -> output_string out_channel "noVid"
	| [i] -> output_string out_channel ("\"" ^ i ^ "\"")
	| i::l -> output_string out_channel ("\"" ^ i ^ "\", ");
	    of_identifier_list l
    and of_lhs_list =
      (** Translate a list of left hand side expressions a list of
	  Attribute identifiers. *)
      function
	  [] ->
	    output_string out_channel "noVid"
	| [LhsVar(_, i)] ->
	    output_string out_channel ("\"" ^ i ^ "\"")
	| [LhsAttr(_, i, c)] ->
	    output_string out_channel ("( \"" ^ i ^ "\" @@ \"") ;
	    of_type c ;
	    output_string out_channel "\" )"
	| LhsVar(_, i)::l ->
	    output_string out_channel ("\"" ^ i ^ "\"") ;
	    of_lhs_list l
	| LhsAttr(_, i, c)::l ->
	    output_string out_channel ("( \"" ^ i ^ "\" @@ \"") ;
	    of_type c ;
	    output_string out_channel "\" )" ;
	    of_lhs_list l
    and of_statement cls stmt =
      let open_paren prec op_prec =
	if prec < op_prec then output_string out_channel "( " ;
      and close_paren prec op_prec =
	if prec < op_prec then output_string out_channel " )" ;
      in let rec print prec =
	function
	    Skip _ -> output_string out_channel "skip"
	  | Assert (_, _) -> output_string out_channel "skip"
	  | Await (note, e) -> output_string out_channel "( await ";
	      of_expression e;
	      output_string out_channel " )"
	  | Release _ -> output_string out_channel "release"
	  | Assign (_, i, e) ->
	      of_lhs_list i;
	      output_string out_channel " ::= " ;
	      of_expression_list e
	  | SyncCall _ -> assert false
	  | AwaitSyncCall _ -> assert false
	  | AsyncCall (_, None, _, _, _) -> assert false
	  | AsyncCall (_, Some l, c, m, a) ->
	      output_string out_channel ("\"" ^ l ^ "\"") ;
	      output_string out_channel " ! ";
	      of_expression c ;
	      output_string out_channel (" . \"" ^ m ^ "\" ( ") ;
	      of_expression_list a;
	      output_string out_channel " )"
	  | Reply (_, l, o) ->
	      output_string out_channel ("( \"" ^ l ^ "\" ? ( ") ;
	      of_lhs_list o;
	      output_string out_channel " ) ) "
	  | Free (_, l) -> output_string out_channel ("free( \"" ^ l ^ "\" )")
	  | LocalSyncCall _ -> assert false
	  | AwaitLocalSyncCall _ -> assert false
	  | LocalAsyncCall (_, None, _, _, _, _) -> assert false
	  | LocalAsyncCall (_, Some l, m, None, None, i) ->
	      (* An unqualified local synchronous call should use this in
		 order to get late binding correct. *)
	      output_string out_channel ("( \"" ^ l ^ "\" ! \"this\" . \"" ^ m ^ "\" (");
	      of_expression_list i;
	      output_string out_channel " ) ) "
	  | LocalAsyncCall (_, Some l, m, lb, ub, i) ->
	      output_string out_channel ("( \"" ^ l ^ "\" ! \"" ^ m ^ "\" ") ;
	      (match lb with
		  None -> output_string out_channel ("@ \"" ^ cls ^ "\" ")
		| Some n -> output_string out_channel ("@ \"" ^ n ^ "\" "));
	      (match ub with
		  None -> ()
		| Some n -> output_string out_channel ("<< \"" ^ n ^ "\" "));
	      output_string out_channel "( " ;
	      of_expression_list i;
	      output_string out_channel " ) ) "
	  | Tailcall (_, m, l, u, i) ->
	      output_string out_channel ( "\"" ^ m ^ "\"");
	      (match l with None -> () | Some n -> output_string out_channel (" @ \"" ^ n ^ "\""));
	      (match u with None -> () | Some n -> output_string out_channel (" << \"" ^ n ^ "\""));
	      output_string out_channel " ( " ;
	      of_expression_list i;
	      output_string out_channel " )"
	  | If (_, c, t, f) ->
	      output_string out_channel "if "; of_expression c;
	      output_string out_channel " th "; print 25 t;
	      output_string out_channel " el "; print 25 f;
	      output_string out_channel " fi"
	  | While (_, c, _, b) ->
	      output_string out_channel "while " ;
	      of_expression c;
	      output_string out_channel " do ";
	      print 25 b;
	      output_string out_channel " od "
	  | Sequence (_, s1, s2) ->
	      let op_prec = 25 in
		open_paren prec op_prec ;
		print op_prec s1; 
		output_string out_channel " ; ";
		print op_prec s2; 
		close_paren prec op_prec
	  | Merge (_, l, r) ->
	      let op_prec = 29 in
		open_paren prec op_prec ;
		print op_prec l; 
		output_string out_channel " ||| ";
		print op_prec r; 
		close_paren prec op_prec
	  | Choice (_, l, r) ->
	      let op_prec = 27 in
		open_paren prec op_prec ;
		print op_prec l; 
		output_string out_channel " [] ";
		print op_prec r; 
		close_paren prec op_prec
      in print 25 stmt
    and of_attribute a =
      output_string out_channel ("(" ^ a.var_name ^ ": ");
      (match a.var_init with
	  None -> output_string out_channel "null"
	| Some e -> of_expression e);
      output_string out_channel ")"
    and of_attribute_list =
      function
	  [] ->  output_string out_channel "none"
	| [a] -> of_attribute a
	| a::l -> of_attribute a; output_string out_channel ", ";
	    of_attribute_list l
    and of_inherits =
      function
	  (i, l) -> output_string out_channel ("\"" ^ i ^ "\" < ");
	    of_expression_list l;
	    output_string out_channel " > "
    and of_inherits_list =
      function
	  [] -> output_string out_channel "noInh"
	| [i] -> of_inherits i
	| i::r -> of_inherits i;
	    output_string out_channel " ## ";
	    of_inherits_list r
    and of_parameter_list =
      function
	  [] -> output_string out_channel "noVid"
	| [v] -> output_string out_channel ("\"" ^ v.var_name ^ "\"")
	| v::r -> output_string out_channel ("\"" ^ v.var_name ^ "\" , ");
	    of_parameter_list r
    and of_class_attribute_list =
      function
	  [] -> output_string out_channel "noSubst" 
	| [v] -> output_string out_channel ("\"" ^ v.var_name ^ "\" |-> null")
	| v::r -> output_string out_channel ("\"" ^ v.var_name ^ "\" |-> null , ");
	    of_class_attribute_list r
    and of_method_return =
      function
	  [] -> output_string out_channel "emp" 
	| [n] -> output_string out_channel ("\"" ^ n.var_name ^ "\"")
	| n::l -> output_string out_channel ("\"" ^ n.var_name ^ "\" # ");
            of_method_return l
    and of_method cls m =
      output_string out_channel ("\n  < \"" ^ m.meth_name ^ "\" : Mtdname | Param: ");
      of_parameter_list m.meth_inpars;
      output_string out_channel ", Latt: " ;
      of_class_attribute_list (m.meth_inpars @ m.meth_outpars @ m.meth_vars);
      output_string out_channel ", Code: " ;
      ( match m.meth_body with
	  None -> output_string out_channel "skip"
	| Some s -> of_statement cls s ;
	    output_string out_channel " ; return ( ";
	    of_method_return m.meth_outpars;
	    output_string out_channel " )" ) ;
      output_string out_channel " >"
    and of_method_list cls =
      function
	  [] -> output_string out_channel "noMtd" 
	| [m] -> of_method cls m
	| m::r -> of_method cls m ;
	    output_string out_channel " *" ;
	    of_method_list cls r
    and of_with_defs cls ws =
      let methods = List.flatten (List.map (function w -> w.With.methods) ws)
      in
	of_method_list cls methods
    and of_class c =
      output_string out_channel ("< \"" ^ c.Class.name ^ "\" : Cl | Inh: ");
      of_inherits_list c.Class.inherits;
      output_string out_channel ", Par: ";
      of_parameter_list c.Class.parameters;
      output_string out_channel ", Att: ";
      of_class_attribute_list (c.Class.parameters @ c.Class.attributes);
      output_string out_channel ", Mtds: ";
      of_with_defs c.Class.name c.Class.with_defs;
      output_string out_channel ", Ocnt: 0 >\n\n"
    and of_interface i = ()
    and of_exception e = ()
    and of_datatype d = ()
    and of_declaration =
      function
	  Class c -> of_class c
	| Interface i -> of_interface i
	| Exception e -> of_exception e
	| Datatype d -> of_datatype d
    and of_decl_list =
      function
	  [] -> output_string out_channel "noConf\n"
	| [d] -> of_declaration d
	| d::l -> of_declaration d; of_decl_list l
    in
      (** Convert an abstract syntax tree l of a creol program to a
	  representation for the Maude CMC and write the result to the
	  output channel out. *)
      if options.modelchecker then
	output_string out_channel "load creol-modelchecker\n"
      else
	output_string out_channel "load creol-interpreter\n";
      output_string out_channel
	("mod PROGRAM is\npr " ^ (if options.modelchecker then
	  "CREOL-MODEL-CHECKER" else "CREOL-INTERPRETER") ^
	    " .\nop init : -> Configuration [ctor] .\neq init =\n") ;
      of_decl_list input ;
      begin
	match options.main with
	    None -> ()
	  | Some m ->
	      output_string out_channel ("main( \"" ^ m ^ "\" , emp )\n")
      end ;
      output_string out_channel ".\nendm\n" ;
      if options.modelchecker then
	begin
	  output_string out_channel "\n\nmod PROGRAM-CHECKER is\n  protecting MODEL-CHECKER .\n  protecting PROGRAM .\n  protecting CREOL-PREDICATES .\nendm\n"
	end ;
      if options.red_init then output_string out_channel "\nred init .\n" ;
      flush out_channel

end
