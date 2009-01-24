(*
 * CMCParser.ml -- Parse the output of the Maude interpreter.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2008 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)


open Creol

(** This defines the stream-based token for the CMC output. *)
exception Eof of string

exception BadToken of string * int * string

type token =
  | Key of string * int
  | Property of string * int
  | Int of Big_int.big_int * int
  | Float of float * int
  | Str of string * int
  | LParen of int
  | RParen of int
  | Comma of int
  | Semi of int
  | Colon of int
  | DColon of int
  | Lt of int
  | Gt of int
  | Question of int
  | At of int
  | Box of int
  | LBrace of int
  | Bar of int
  | MapsTo of int
  | Merge of int
  | RBrace of int





let get_token_line =
  function
      Key (_, line) | Property (_, line) | Str (_, line)
    | Int (_, line) | Float (_, line)
    | LParen line | RParen line
    | Comma line | Semi line | Colon line | DColon line
    | Lt line | Gt line | Question line | At line
    | Box line | LBrace line | Bar line
    | MapsTo line | Merge line | RBrace line -> line





let get_token_name =
  function
    | Key (name, _) -> "<<key: " ^ name ^ ">>"
    | Property(name, _) -> "<<property: " ^ name ^ ">>"
    | Str (s, _) -> "<<string: '" ^ s ^ "'>>"
    | Int (i, _) -> "<<integer: " ^ (Big_int.string_of_big_int i) ^ ">>"
    | Float (f, _) -> "<<real: " ^ (string_of_float f) ^ ">>"
    | LParen _ -> "("
    | RParen _ -> ")"
    | Comma _ -> ","
    | Semi _ -> ";"
    | Colon _ -> ":"
    | DColon _ -> "::"
    | Lt _ -> "<"
    | Gt _ -> ">"
    | Question _ -> "?"
    | At _ -> "@"
    | Box _ -> "[]"
    | LBrace _ -> "{"
    | Bar _ -> "|"
    | MapsTo _ -> "|->"
    | Merge _ -> "|||"
    | RBrace _ -> "}"

let error_tokens input =
  let tl = Stream.npeek 5 input in
  let ts = String.concat ", "
    (List.map (fun t -> "`" ^ (get_token_name t) ^"'") tl)
  in
    ts

(* A string either represents a string value, an attribute or variable
   name or a meta-attribute name.  Whether it is a string value or
   an attribute or a meta-attribute name depends on the context.
   A meta-attribute is distinguished from an attribute name by the
   dot at its start. The following function checks whether a string
   starts with a dot. *)

let starts_with_dot_p str =
  if (String.length str) > 1 then
    if '.' = (String.get str 0) then
      true
    else
      false
  else
    false




(* Tokenize a stream.  The input is a stream of characters.  The output
   is a stream of tokens. *)
let token input =
  let line = ref 1 in
  let initial_buffer = String.create 256 in
  let buffer = ref initial_buffer in
  let bufpos = ref 0 in
  let reset_buffer () = buffer := initial_buffer; bufpos := 0 in
  let store c =
    if !bufpos >= String.length !buffer then
      begin
	let newbuffer = String.create (2 * !bufpos)
	in
	  String.blit !buffer 0 newbuffer 0 !bufpos;
	  buffer := newbuffer
      end;
    String.set !buffer !bufpos c;
    incr bufpos in
  let rec junk stream =
    let () = Stream.junk stream in
      match Stream.peek stream with
	  Some (' ' | '\009' | '\026' | '\012') -> junk stream
	| Some ( '\013' | '\010' ) -> incr line; junk stream 
	| _ -> ()
  in
  let get_string () =
    let s = String.sub !buffer 0 !bufpos in buffer := initial_buffer; s in
    let rec next_token stream =
      match Stream.peek stream with
	  Some (' ' | '\009' | '\026' | '\012') ->
	    junk stream; next_token stream
	| Some ( '\013' | '\010' ) ->
	    Stream.junk stream; incr line; next_token stream 
	| Some ('$' | 'A'..'Z' | 'a'..'z' | '_' | '\192'..'\255' as c) ->
	    Stream.junk stream ; reset_buffer () ; store c; parse_key stream
	| Some ('0'..'9' as c) ->
	    Stream.junk stream; reset_buffer (); store c; parse_number stream
	| Some '@' -> let () = Stream.junk input in Some(At !line)
	| Some '(' -> Stream.junk stream; Some(LParen !line)
	| Some ')' -> Stream.junk stream; Some(RParen !line)
	| Some ',' -> Stream.junk stream; Some(Comma !line)
	| Some ';' -> Stream.junk stream; Some(Semi !line)
	| Some '"' -> Stream.junk stream; reset_buffer(); parse_string stream
	| Some ':' -> 
	    let () = Stream.junk stream in
	      begin
		match Stream.peek stream with
		  | Some ':' ->
		      let () = Stream.junk stream in
			Some (DColon !line)
		  | _ ->
		      Some (Colon !line)
	      end
	| Some '<' -> Stream.junk stream; Some (Lt !line)
	| Some '>' -> Stream.junk stream; Some (Gt !line)
	| Some '?' -> Stream.junk stream; Some (Question !line)
	| Some '[' ->
	    begin
	      (* Maude may emit a newline between '[' and ']' *)
	      let () = junk stream  in
		match Stream.peek stream with
		  | Some ']' -> 
		      let () = Stream.junk stream in Some (Box !line)
		  | t ->
		      raise (BadToken (Char.escaped '[', !line, "Tokenizer"))
	    end
	| Some '{' -> Stream.junk stream; Some (LBrace !line)
	| Some '|' -> Stream.junk stream; 
	    begin
              match Stream.npeek 2 stream with
                | [ '-'; '>'] -> Stream.junk stream; Stream.junk stream;
			Some (MapsTo !line)
                | [ '|'; '|'] -> Stream.junk stream; Stream.junk stream;
			Some (Merge !line)
		| _ -> Some (Bar !line)
            end
	| Some '}' -> Stream.junk stream; Some (RBrace !line)
	| Some c -> raise (BadToken (Char.escaped c, !line, "Tokenizer"))
	| None -> None
    and parse_key stream =
      match Stream.peek stream with
	  Some ('0'..'9' | 'A'..'Z' | 'a'..'z' | '_' | '\192'..'\255' as c) ->
	    Stream.junk stream; store c; parse_key stream
	| Some ':' -> Stream.junk stream; Some (Property (get_string (), !line))
	| _ -> Some (Key (get_string (), !line))
    and parse_string stream =
      match Stream.peek stream with
	  Some('"') -> Stream.junk stream; Some(Str(get_string(), !line))
	| Some ('\010' | '\013') -> raise (Stream.Error "")
	| Some c -> Stream.junk stream; store c; parse_string stream
	| _ -> raise Stream.Failure
    and parse_number stream =
      match Stream.npeek 2 stream with
	  ('0'..'9' as c)::_ ->
	    Stream.junk stream;
	    store c;
	    parse_number stream
	| ['.'; '0'..'9' | 'e' | 'E' ] ->
            Stream.junk stream; store '.'; parse_decimal_part stream
	| ['.'; _ ] ->
            Some (Int (Big_int.big_int_of_string (get_string ()), !line))
	| ('e' | 'E')::_ ->
	    Stream.junk stream;
	    store 'e';
	    parse_exponent_part stream
	| _ ->
	    Some (Int (Big_int.big_int_of_string (get_string ()), !line))
    and parse_decimal_part stream =
      match Stream.peek stream with
	  Some ('0'..'9' as c) ->
	    Stream.junk stream;
	    store c;
	    parse_decimal_part stream
	| Some ('e' | 'E') ->
	    Stream.junk stream;
	    store 'e';
	    parse_exponent_part stream
	| _ -> Some(Float (float_of_string (get_string ()), !line))
    and parse_exponent_part stream =
      match Stream.peek stream with
	  Some ('+' | '-' as c) ->
	    Stream.junk stream;
	    store c;
	    parse_end_exponent_part stream
	| _ -> parse_end_exponent_part stream
    and parse_end_exponent_part stream =
      match Stream.peek stream with
	  Some ('0'..'9' as c) ->
	    Stream.junk stream;
	    store c;
	    parse_end_exponent_part stream
	| _ -> Some(Float (float_of_string (get_string ()), !line))
    in
      Stream.from (fun count -> next_token input)




(*s CMC Parser.

  This defines the LL(2) predictive recursive descent parser for
  object configurations. Since the parser does not use any backup, it
  can parse an object configuration in linear time. *)


(* The parser creates property maps. *)

module PropMap = Map.Make(String)


(* The type of the value of this map is given below. *)

type t =
  | Cls of Class.t
  | Mtd of Method.t
  | Obj of Object.t

type v =
  | Ignored
  | Attr of (string * Expression.t) list
  | Code of Statement.t
  | Inh of Inherits.t list
  | Mtds of Method.t list
  | Parameters of string list
  | Process of Process.t
  | ProcessQueue of Process.t list

let get_attr =
  function
    | Attr res -> res
    | _ -> assert false

let get_code =
  function
    | Code res -> res
    | _ -> assert false

let get_inh =
  function
    | Inh res -> res
    | _ -> assert false

let get_mtds =
  function
    | Mtds res -> res
    | _ -> assert false

let get_parameters =
  function
    | Parameters res -> res
    | _ -> assert false

let get_process =
  function
    | Process res -> res
    | _ -> assert false

let get_process_queue =
  function
    | ProcessQueue res -> res
    | _ -> assert false

let vardecl_of_binding (n, i) =
  { VarDecl.name = n; var_type = Type.data; init = Some i; file = ""; line = 0 }

let vardecl_of_name n =
  { VarDecl.name = n; var_type = Type.data; init = None; file = ""; line = 0 }

let parse name input =
  let build_term oid cid props =
    match cid with
      | "~Class" ->
	  let p = get_parameters (PropMap.find "Param" props)
	  and i = get_inh (PropMap.find "Inh" props)
	  and m = get_mtds (PropMap.find "Mtds" props)
	  and a = get_attr (PropMap.find "Att" props)
	  in
	    Cls { Class.name = oid ;
		  parameters = (List.map vardecl_of_name p) ;
		  inherits = i ;
		  contracts = [] ;
		  implements = [] ;
		  attributes = (List.map vardecl_of_binding a);
		  invariants = [] ;
		  with_defs = [{ With.co_interface = Type.any;
				 methods = m;
				 invariants = [];
                                 file = ""; line = 0}] ;
		  pragmas = [];
		  file = "";
		  line = 0 }
      | "~Method" ->
	  let c = get_code (PropMap.find "Code" props)
	  and p = get_parameters (PropMap.find "Param" props)
	  and a = get_attr (PropMap.find "Att" props)
	  in
	    Mtd { Method.name = oid;
		  coiface = Type.any;
		  inpars = List.map vardecl_of_name p;
		  outpars = [];
		  requires = Expression.Bool (Expression.make_note (), true);
		  ensures = Expression.Bool (Expression.make_note (), true);
		  vars = (List.map vardecl_of_binding a);
		  body = Some c;
		  location = "";
		  file = "";
                  line = 0 }
      | t ->
	  let a = get_attr (PropMap.find "Att" props)
	  and p = get_process (PropMap.find "Pr" props)
	  and q = get_process_queue (PropMap.find "PrQ" props)
	  in
	    Obj { Object.name = oid;
		  cls = Type.Basic t;
		  attributes = (List.map vardecl_of_binding a);
		  process = p;
		  process_queue = q;
		  hidden = false }
  in
  let rec parse_configuration input =
    match Stream.peek input with
      | Some Lt _ ->
	  let res =
	    match parse_object_term input with 
	      | Cls c -> Declaration.Class c
	      | Obj o -> Declaration.Object o
	      | _ -> assert false
	  in
	    res::(parse_configuration input)
      | Some Key (_, _) ->
	  let res = parse_expression input in
	    parse_configuration input
      | _ ->
	  []
  and parse_object_term_list input =
    match Stream.peek input with
      | Some Key (_, _) ->
	  []
      | Some Lt _ ->
	  begin
	    let t = parse_object_term input in
	      match Stream.npeek 2 input with
		| [Comma _; Property _] | (Gt _)::_ ->
		    [t]
		| (Comma _)::_ ->
		    let () = Stream.junk input in
		    let r = parse_object_term_list input in
		      t::r
		| _ -> [t]
	  end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "<<key>>, `<'"))
      | None ->
	  raise (Eof "")
  and parse_object_term input =
    let () = junk_left_bracket input in
    let oid = parse_oid input in
    let () = junk_colon input in
    let cid = parse_cid input in
    let () = junk_bar input in
    let props = parse_properties PropMap.empty input in
    let () = junk_right_bracket input in
      build_term oid cid props
  and parse_oid input =
    match Stream.peek input with
      | Some Key ("ob", _) ->
          let () = Stream.junk input in
	  let () = junk_lparen input in
	  let s = parse_string input in
	  let () = junk_rparen input in
	    s
      | Some Str (v, _) ->
	  let () = Stream.junk input in v
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "OID: <<key>>,<<string>>"))
      | None -> raise (Eof "")
  and parse_cid input =
    match Stream.peek input with
      | Some Key (v, _) ->
	  let () = Stream.junk input in
	    "~" ^ v
      | Some Str (s, _) ->
	  let () = Stream.junk input in
	    s
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "CID: <<key>>,<<string>>"))
      | None -> raise (Eof "")
  and parse_properties map input =
    match Stream.peek input with
      | Some Property (p, _) ->
	  begin
	    let v = parse_property input in
	    let map' = PropMap.add p v map in
	      match Stream.npeek 2 input with
		| [ Comma _; Property _] ->
		    let () = Stream.junk input in
		      parse_properties map' input
		| _ ->
		    map'
	  end
      | Some _ -> assert false
      | None -> raise (Eof "")
  and parse_property input =
    match Stream.peek input with
      | Some Property ("Att", _) ->
	  let () = Stream.junk input in
	  let v = parse_substitution input in
	    Attr v
      | Some Property ("Code", _) ->
	  let () = Stream.junk input in
	  let v = parse_merge_statement input in
	    Code v
      | Some Property ("Inh", _) ->
	  let () = Stream.junk input in
	  let v = parse_inherit_list input in
	    Inh v
      | Some Property ("Mtds", _) ->
	  let () = Stream.junk input in
	    Mtds (List.map (function (Mtd m) -> m | _ -> assert false)
		    (parse_object_term_list input))
      | Some Property ("Param", _) ->
	  let () = Stream.junk input in
	  let v = parse_parameters input in
	    Parameters v
      | Some Property ("Pr", _) ->
	  let () = Stream.junk input in
	  let p = parse_process input in
	    Process p
      | Some Property ("PrQ", _) ->
	  let () = Stream.junk input in
	  let q = parse_process_queue input in
	    ProcessQueue q
      | Some Property (p, _) ->
	  let () = Stream.junk input in
	  let () = junk_property input in
	    Ignored
      | Some t ->
	  let tl = error_tokens input in
	    raise (BadToken (tl, get_token_line t, "properties"))
      | None -> raise (Eof "")
  and junk_property input =
    match Stream.peek input with
      | Some Lt _ ->
	  begin
	    let _ = parse_object_term input in
	      match Stream.npeek 2 input with
		| [ Comma _ ; Property _ ] ->
		    ()
		| (Comma _)::_ ->
		    let () = Stream.junk input in
		      junk_property input
		| _ ->
		    ()
	  end
      | Some LBrace _ ->
	  begin
	    let _ = parse_process input in
	      match Stream.npeek 2 input with
		| [ Comma _ ; Property _ ] ->
		    ()
		| (Comma _)::_ ->
		    let () = Stream.junk input in
		      junk_property input
		| _ ->
		    ()
	  end
      | Some t ->
	  begin
	    let p input =
	      match Stream.npeek 2 input with
		| [Comma _; Property _ ] | (Gt _)::_ | (RBrace _)::_ | [] ->
		    false
		| _ ->
		    true
	    in
	      while p input do
		Stream.junk input
	      done
	  end
      | None -> raise (Eof "")
  and parse_inherit_list input =
    match Stream.peek input with
      | Some Key ("noInh", _) ->
	  let () = Stream.junk input in
	    []
      | Some Str (c, _) ->
	  begin
	    let i = parse_inherit input in
	      match Stream.npeek 2 input with
		| [ Comma _; Str _] ->
		    let () = Stream.junk input in
		    let l = parse_inherit_list input in
		      i::l
		| _ -> [i]
	  end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "<<string>>"))
      | None -> raise (Eof "")
  and parse_inherit input =
    let n = parse_string input in
    let () = junk_left_bracket input in
    let a = parse_expression_list input in
    let () = junk_right_bracket input in
      { Inherits.name = n; arguments = a }
  and parse_process_queue input =
    match Stream.peek input with
      | Some LBrace _ ->
	  begin
	    let p = parse_process input in
	      match Stream.npeek 2 input with
		| [ Comma _; LBrace _] ->
		    let () = Stream.junk input in
		    let r = parse_process_queue input in
		      p::r
		| _ -> [p]
	  end
      | Some Key ("noProc", _) ->
	  let () = Stream.junk input in
	    []
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "noProc, {"))
      | None ->
	  raise (Eof "")
  and parse_process input =
    match Stream.peek input with
      | Some Key ("idle", _) ->
	  begin
	    let () = Stream.junk input in
	      { Process.attributes = [];
		code = Statement.Skip (Statement.make_note ()) }
	  end
      | Some LBrace _ ->
	  let () = Stream.junk input in
	  let s = parse_substitution input in
          let () = junk_bar input in
	  let p = parse_merge_statement input in
	  let () = junk_right_brace input in
	    { Process.attributes = List.map vardecl_of_binding s; code = p }
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "{"))
      | None ->
	  raise (Eof "")
  and parse_substitution input =
    match Stream.peek input with
      | Some Key ("noSubst", _) ->
	  let () = Stream.junk input in
	    []
      | Some Str (s, _) ->
	  begin
	    let () = Stream.junk input in
	    let () = junk_mapsto input in
	    let v = parse_expression input in
	      match Stream.npeek 2 input with
		| [ Comma _; Str _ ] ->
		    let () = Stream.junk input in
		      (s, v)::(parse_substitution input)
		| _ ->
		    [(s,v)]
	  end
      |  Some t ->
	   raise (BadToken (error_tokens input, get_token_line t,
			    "noSubst, <<string>>"))
      | None ->
	  raise (Eof "")
  and parse_parameters input =
    match Stream.peek input with
      | Some Key ("noVid", _) ->
	  let () = Stream.junk input in
	    []
      | Some Str (s, _) ->
	  begin
	    let () = Stream.junk input in
	      match Stream.npeek 2 input with
		| [ Comma _; Str _ ] ->
		    let () = Stream.junk input in
		      s::(parse_parameters input)
		| _ -> [s]
	  end
      |  Some t ->
	   raise (BadToken (error_tokens input, get_token_line t,
			    "noSubst, <<string>>"))
      | None ->
	  raise (Eof "")
  and parse_merge_statement input =
    let lhs = parse_choice_statement input in
      match Stream.peek input with
	| Some Merge _ | Some Key ("MERGER", _) ->
	    let () = Stream.junk input in
	    let rhs = parse_merge_statement input in
	      Statement.Merge (Statement.make_note (), lhs, rhs)
	| _ -> lhs
  and parse_choice_statement input =
    let lhs = parse_sequential_statement input in
      match Stream.peek input with
	| Some Box _ ->
	    let () = Stream.junk input in
	    let rhs = parse_choice_statement input in
	      Statement.Choice (Statement.make_note (), lhs, rhs)
	| _ -> lhs
  and parse_sequential_statement input =
    let lhs = parse_statement input in
      match Stream.peek input with
	| Some Semi _ ->
	    let () = Stream.junk input in
	    let rhs = parse_sequential_statement input in
	      Statement.Sequence (Statement.make_note (), lhs, rhs)
	| _ -> lhs
  and parse_statement input =
    match Stream.peek input with
      | Some Key ("skip", _) ->
	  Stream.junk input;
	  Statement.Skip (Statement.make_note ())
      | Some Key ("commit", _) ->
	  Stream.junk input;
	  assert false
      | Some Key ("release", _) ->
	  Stream.junk input;
	  Statement.Release (Statement.make_note ())
      | Some Key ("await", _) ->
	  let () = Stream.junk input in
	  let c = parse_expression input in
	    Statement.Await (Statement.make_note (), c)
      | Some Key ("posit", _) ->
	  let () = Stream.junk input in
	  let c = parse_expression input in
	    Statement.Posit (Statement.make_note (), c)
      | Some Key (("assert" | "failure"), _) ->
	  (* We map the failure back to the assert statement for now. *)
	  let () = Stream.junk input in
	  let c = parse_expression input in
	    Statement.Assert (Statement.make_note (), c)
      | Some Key (("assign" | "$assign"), _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let lhs = parse_lhs_list input in
	  let () = junk_semicolon input in
	  let rhs = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.Assign (Statement.make_note (), lhs, rhs)
      | Some Key ("new", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let lhs = parse_lhs input in
	  let () = junk_semicolon input in
	  let t = parse_type input in
	  let () = junk_semicolon input in
	  let args = parse_expression_list input in
	  let () = junk_rparen input in
	  let e = Expression.New (Expression.make_note (), t, args) in
	    Statement.Assign (Statement.make_note (), [lhs], [e])
      | Some Key ("call", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_lhs input in
	  let () = junk_semicolon input in
	  let c = parse_expression input in
	  let () = junk_semicolon input in
	  let m = parse_method_name input in
	  let () = junk_semicolon input in
	  let a = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.AsyncCall (Statement.make_note (), Some l, c, m,
				 Type.default_sig (), a)
      | Some Key ("static", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_lhs input in
	  let () = junk_semicolon input in
	  let m = parse_method_name input in
	  let () = junk_semicolon input in
	  let lb = parse_bound input in
	  let () = junk_semicolon input in
	  let ub = parse_bound input in
	  let () = junk_semicolon input in
	  let a = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.LocalAsyncCall (Statement.make_note (), Some l, m,
				      Type.default_sig (), lb, ub, a)
      | Some Key (("multicast" | "$multicast"), _) ->
          let () = Stream.junk input in
          let () = junk_lparen input in
          let e = parse_expression input in
          let () = junk_semicolon input in
          let m = parse_method_name input in
          let () = junk_semicolon input in
          let a = parse_expression_list input in
          let () = junk_rparen input in
            Statement.MultiCast (Statement.make_note (), e, m,
				 Type.default_sig (), a)
      | Some Key ("get", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let e = parse_expression input in
	  let () = junk_semicolon input in
	  let r = parse_lhs_list input in
	  let () = junk_rparen input in
	    Statement.Get (Statement.make_note (), e, r)
      | Some Key ("return", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let a = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.Return (Statement.make_note (), a)
      | Some Key ("free", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_lhs_list input in
	  let () = junk_rparen input in
	    Statement.Free (Statement.make_note (), l)
      | Some Key ("tailcall", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let c = parse_expression input in
	  let () = junk_semicolon input in
          let m = parse_method_name input in
	  let () = junk_semicolon input in
	  let a = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.Tailcall (Statement.make_note (), c, m,
				Type.default_sig (), a)
      | Some Key ("statictail", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let m = parse_method_name input in
	  let () = junk_semicolon input in
	  let lb = parse_bound input in
	  let () = junk_semicolon input in
	  let ub = parse_bound input in
          let () = junk_semicolon input in
	  let a = parse_expression_list input in
	  let () = junk_rparen input in
	    Statement.StaticTail (Statement.make_note (), m,
				  Type.default_sig (), lb, ub, a)
      | Some Key ("$accept", _) ->
	  let () = Stream.junk input in
	  let l = parse_expression input in
	    assert false (* Statement.Accept (Statement.make_note (), l) *)
      | Some Key ("$cont", _) ->
	  let () = Stream.junk input in
	  let l = parse_expression input in
	    Statement.Continue (Statement.make_note (), l)
      | Some Key ("if", _) ->
	  let () = Stream.junk input in
	  let c = parse_expression input in
	  let () = junk_keyword "th" input in
	  let th = parse_merge_statement input in
	  let () = junk_keyword "el" input in
	  let el = parse_merge_statement input in
	  let () = junk_keyword "fi" input in
	    Statement.If (Statement.make_note (), c, th, el)
      | Some Key ("while", _) ->
	  let () = Stream.junk input in
	  let c = parse_expression input in
	  let t = Expression.Bool (Expression.make_note (), true) in
	  let () = junk_keyword "do" input in
	  let d = parse_merge_statement input in
	  let () = junk_keyword "od" input in
	    Statement.While (Statement.make_note (), c, t, d)
      | Some LParen _ ->
	  let () = Stream.junk input in
	  let s = parse_merge_statement input in
	  let () = junk_rparen input in
	    s
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "statement"))
      | None -> raise (Eof "")
  and parse_method_name input =
    match Stream.peek input with
      | Some Str (m, _) ->
	  begin
	    let () = Stream.junk input in
	      m
	  end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "method_name"))
      | None -> raise (Eof "")
  and parse_expression input =
    match Stream.peek input with
      | Some Key ("bool", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let r =
	    match Stream.peek input with
	      | Some Key ("true", _) ->
		  Expression.Bool (Expression.make_note (), true)
	      | Some Key ("false", _) ->
		  Expression.Bool (Expression.make_note (), false)
	      | Some t -> raise (BadToken (error_tokens input,
					   get_token_line t, "true, false"))
	      | None -> raise (Eof "")
	  in
	  let () = Stream.junk input in
	  let () = junk_rparen input in
	    r
      | Some Key ("list", line) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_expression_list input in
	  let () = junk_rparen input in
	    Expression.ListLit (Expression.make_note (), l)
      | Some Key ("int", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let i = parse_integer input in
	  let () = junk_rparen input in
	    Expression.Int (Expression.make_note (), i)
      | Some Key ("label", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let o = parse_expression input in
	  let () = junk_comma input in
	  let i = parse_integer input in
	  let i' = Expression.Int (Expression.make_note (), i) in
	  let () = junk_rparen input in
	    Expression.LabelLit (Expression.make_note (), [o; i'])
      | Some Key ("map", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let b = parse_bindings input in
	  let () = junk_rparen input in
	    Expression.MapLit (Expression.make_note (), b)
      | Some Key ("now", _) ->
	  let () = Stream.junk input in
	    Expression.Now (Expression.make_note ())
      | Some Key ("null", _) ->
	  let () = Stream.junk input in
	    Expression.Null (Expression.make_note ())
      | Some Key ("ob", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let r = parse_string input in
	  let () = junk_rparen input in
	    Expression.ObjLit (Expression.make_note (), r)
      | Some Key ("set", line) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_elements input in
	  let () = junk_rparen input in
	    Expression.SetLit (Expression.make_note (), l)
      | Some Key ("str", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let r = parse_string input in
	  let () = junk_rparen input in
	    Expression.String (Expression.make_note (), r)
      | Some Str (f, _) ->
	  begin
	    Stream.junk input;
	    match Stream.peek input with
	      | Some LParen _ ->
		  let () = Stream.junk input in
		  let l = parse_expression_list input in
	          let () = junk_rparen input in
		    Expression.FuncCall (Expression.make_note (), f, l)
	      | Some At _ ->
		  let () = Stream.junk input in
		  let t = parse_type input in
		    Expression.StaticAttr (Expression.make_note (), f, t)
	      | _ ->
		  begin
		    match f with
		      | "this" ->
			  Expression.This (Expression.make_note ())
		      | "caller" ->
			  Expression.Caller (Expression.make_note ())
		      | _ ->
			  Expression.Id (Expression.make_note (), f)
		  end
	  end
      | Some Question _ ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let l = parse_expression input in
	  let () = junk_rparen input in
	    Expression.Label (Expression.make_note (), l)
      | Some LParen _ ->
	  let () = Stream.junk input in
	  let e = parse_expression input in
	  let () = junk_rparen input in
	    e
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "expression"))
      | None -> raise (Eof "")
  and parse_expression_list input =
    let rec do_parse input =
      let e = parse_expression input in
	match Stream.peek input with
	  | Some DColon _ ->
	      Stream.junk input ;
	      let l = do_parse input in
		e::l
	  | _ -> [e]
    in
      match Stream.peek input with
	| Some Key ("emp", _) -> let () = Stream.junk input in []
	| _ -> do_parse input
  and parse_bindings input =
    match Stream.peek input with
      | Some Key ("empty", _) ->
          let () = Stream.junk input in
	    []
      | Some Key ("mapentry", _) ->
	  let () = Stream.junk input in
	  let () = junk_lparen input in
	  let d = parse_expression input in
	  let () = junk_comma input in
	  let r = parse_expression input in
	  let () = junk_rparen input in
	    begin
	      match Stream.peek input with
	        | Some Comma _ ->
		    (d, r)::(parse_bindings input)
	        | _ -> [(d, r)]
	    end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "map"))
      | None -> raise (Eof "")
  and parse_elements input =
    match Stream.peek input with
      | Some Key ("emptyset", _) ->
          let () = Stream.junk input in
	    []
      | _ ->
	  let e = parse_expression input in
	    match Stream.peek input with
	      | Some Colon _ ->
		  e::(parse_elements input)
	      | _ -> [e]
  and parse_lhs_list input =
    match Stream.peek input with
      | Some Key ("noVid", _) ->
	  let () = Stream.junk input in
	    []
      | Some Str _  | Some LParen _ ->
	  begin
	    let lhs = parse_lhs input in
	      match Stream.peek input with
		| Some Comma _ ->
		    let () = Stream.junk input in
		      lhs::(parse_lhs_list input)
		| _ -> [lhs]
	  end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "lhs_list"))
      | None -> raise (Eof "")
  and parse_lhs input =
    match Stream.peek input with
      | Some Str (v, _) ->
	  begin
	    let () = Stream.junk input in
	      match Stream.peek input with
		| Some At _ ->
		    begin
		      let () = Stream.junk input in
		      let t = parse_type input in
			Expression.LhsAttr (Expression.make_note (), v, t)
		    end
		| _ ->
		    Expression.LhsId (Expression.make_note (), v)
	  end
      | Some LParen _ ->
	  let () = Stream.junk input in
	  let lhs = parse_lhs input in
	  let () = junk_rparen input in
	    lhs
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   "lhs"))
      | None -> raise (Eof "")
  and parse_type input =
    match Stream.peek input with
      | Some Str (c, _) ->
	  begin
	    let () = Stream.junk input in
	      Type.Basic c
	  end
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "type"))
      | None ->
	  raise (Eof "")
  and parse_integer input =
    match Stream.peek input with
      | Some Int (i, _) ->
	  let () = Stream.junk input in
	    i
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   ")"))
      | None ->
	  raise (Eof "")
  and parse_bound input =
    match Stream.peek input with
      | Some Key("None", _) -> let () = Stream.junk input in None
      | Some Str _ -> let s = parse_string input in Some s
  and parse_string input =
    match Stream.peek input with
      | Some Str (s, _) ->
	  let () = Stream.junk input in
	    s
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t,
			   ")"))
      | None ->
	  raise (Eof "")
  and junk_keyword kw input =
    match Stream.peek input with
      | Some Key (kw, _) -> Stream.junk input
      | Some t ->
           raise (BadToken (error_tokens input, get_token_line t, kw))
      | None ->
	    raise (Eof "")
  and junk_mapsto input =
    match Stream.peek input with
      | Some MapsTo _ -> Stream.junk input
      | Some t ->
           raise (BadToken (error_tokens input, get_token_line t, "|->"))
      | None ->
	    raise (Eof "")
  and junk_lparen input =
    match Stream.peek input with
      | Some LParen _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "("))
      | None ->
	  raise (Eof "")	
  and junk_colon input =
    match Stream.peek input with
      | Some Colon _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, ":"))
      | None ->
	  raise (Eof "")
  and junk_semicolon input =
    match Stream.peek input with
      | Some Semi _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, ";"))
      | None ->
	  raise (Eof "")
  and junk_comma input =
    match Stream.peek input with
      | Some Comma _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, ","))
      | None ->
	  raise (Eof "")
  and junk_rparen input =
    match Stream.peek input with
      | Some RParen _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, ")"))
      | None ->
	  raise (Eof "")
  and junk_left_bracket input =
    match Stream.peek input with
      | Some Lt _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "<"))
      | None ->
	  raise (Eof "")
  and junk_bar input =
    match Stream.peek input with
      | Some Bar _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "|"))
      | None ->
	  raise (Eof "")
  and junk_right_bracket input =
    match Stream.peek input with
      | Some Gt _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, ">"))
      | None ->
	  raise (Eof "")
  and junk_left_brace input =
    match Stream.peek input with
      | Some LBrace _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "{"))
      | None ->
	  raise (Eof "")
  and junk_right_brace input =
    match Stream.peek input with
      | Some RBrace _ ->
	  Stream.junk input
      | Some t ->
	  raise (BadToken (error_tokens input, get_token_line t, "}"))
      | None ->
	  raise (Eof "")
  in
    match Stream.peek input with
      | Some LBrace _ ->
          let () = junk_left_brace input in
          let c = parse_configuration input in
          let () = junk_right_brace input in
            c
      | _ -> parse_configuration input






(*s The following functions comprise the front-end of the compiler.
  The purpose of the front-end is to perform lexical analysis and
  parsing of the input programs.

  Read the contents from a channel and return a abstract syntax tree
  and measure the time used for it.
*)
let parse_from_channel (name: string) (channel: in_channel) =
  Program.make (parse name (token (Stream.of_channel channel)))


(* Read the contents of a file and return an abstract syntax tree.
*)
let parse_from_file name = parse_from_channel name (open_in name)
