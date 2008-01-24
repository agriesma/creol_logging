(*
 * TreeFree.ml -- Free dead labels.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
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

(*s Free all labels which are not read from.

  Requires life ranges. *)

open Creol
open Expression
open Statement
open VarDecl
open Method

let log l = Messages.message (l + 1)

(* This function tries to fold all constant expressions to literals.

   The current implementation has some limitation:
   \begin{itemize}
   \item Numbers are computed as OCaml integers (30 bits on 32 bit
     platforms and 62 bits on 64 bit platforms).  Overflows are
     unhandled.  This may lead to incorrect compiler output.
   \item Associativity and commutativity is not handled yet.  The
     expression $1+x+1$ is neither folded to $2+x$ nor $x+2$.
   \end{itemize} *)

let optimise_in_statement meth stmt =
  let rec fold_expr = function
    | This _ as e -> e
    | QualifiedThis _ as e -> e
    | Caller _ as e -> e
    | Now _ as e -> e
    | Null _ as e -> e
    | Nil _ as e -> e
    | History _ as e -> e
    | Bool _ as e -> e
    | Int _ as e -> e
    | Float _ as e -> e
    | String _ as e -> e
    | Id _ as e -> e
    | StaticAttr _ as e -> e
    | Tuple (n, l) -> Tuple (n, List.map fold_expr l)
    | ListLit (n, l) -> ListLit (n, List.map fold_expr l)
    | SetLit (n, l) -> SetLit (n, List.map fold_expr l)
    | Unary (n, o, e) ->
        let e' = fold_expr e in
          begin
            match o with
              | Not ->
                  begin match e' with
                    | Bool(_, true) -> Bool(n, false)
                    | Bool(_, false) -> Bool(n, true)
                    | Unary (n', Not, e'') -> Expression.set_note n e''
                    | _ -> Unary (n, o, e')
                  end
              | UMinus ->
                  begin
                    match e' with
                      | Unary (n'', UMinus, e'') -> Expression.set_note n e''
                      | _ -> Unary (n, o, e')
                  end
              | Length ->
                  begin
                    match e' with
                      | Nil _ -> Int (n, 0)
                      | ListLit (_, l) -> Int (n, List.length l)
                      | SetLit (_, []) -> Int (n, 0)
                      | _ -> Unary (n, o, e')
                  end
          end
    | Binary (n, o, l, r) ->
	let l' = fold_expr l
	and r' = fold_expr r
	in
	  begin
	    match o with
		Plus ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv + rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Minus ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv - rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Times  ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv * rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Div ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv / rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Modulo  ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv / rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Power ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Int (n, lv / rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Eq ->
		  if l' = r' then
		    Bool (n, true)
		  else
		    Binary (n, o, l', r')
	      | Ne ->
		  if l' = r' then
		    Bool (n, false)
		  else
		    Binary (n, o, l', r')
	      | Le ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Bool (n, lv <= rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Lt ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Bool (n, lv < rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Ge ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Bool (n, lv >= rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Gt ->
		  begin
		    match (l', r') with
			(Int (_, lv), Int (_, rv)) -> Bool (n, lv > rv)
		      | _ -> Binary (n, o, l', r')
		  end
	      | And  ->
		  begin
		    match (l', r') with
			(Bool (_, false), _) -> Bool (n, false)
		      | (_, Bool (_, false)) -> Bool (n, false)
		      | (Bool(_, true), Bool (_, true)) -> Bool (n, true)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Wedge ->
		  begin
		    match (l', r') with
			(Bool (_, false), _) -> Bool (n, false)
		      | (_, Bool (_, false)) -> Bool (n, false)
		      | (Bool(_, true), Bool (_, true)) -> Bool (n, true)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Or ->
		  begin
		    match (l', r') with
			(Bool (_, true), _) -> Bool (n, true)
		      | (_, Bool (_, true)) -> Bool (n, true)
		      | (Bool(_, false), Bool (_, false)) -> Bool (n, false)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Vee ->
		  begin
		    match (l', r') with
			(Bool (_, true), _) -> Bool (n, true)
		      | (_, Bool (_, true)) -> Bool (n, true)
		      | (Bool(_, false), Bool (_, false)) -> Bool (n, false)
		      | _ -> Binary (n, o, l', r')
		  end
	      | Xor ->
		  if l' = r' then
		    Bool (n, false)
		  else
		    Binary (n, o, l', r')
	      | Implies ->
		  begin
		    match (l', r') with
			(Bool (_, false), _) -> Bool (n, true)
		      | (_, Bool (_, true)) -> Expression. set_note n l'
		      | _ -> Binary (n, o, l', r')
		  end
	      | Iff ->
		  if l' = r' then
		    Bool (n, true)
		  else
		    Binary (n, o, l', r')
	      | Prepend ->
		  begin
		    match (l', r') with
		      | _ -> Binary (n, o, l', r')
		  end
	      | Append ->
		  begin
		    match (l', r') with
		      | _ -> Binary (n, o, l', r')
		  end
	      | Concat ->
		  begin
		    match (l', r') with
		      | _ -> Binary (n, o, l', r')
		  end
	      | Project ->
		  begin
		    match (l', r') with
		      | _ -> Binary (n, o, l', r')
		  end
	      | In ->
		  begin
		    match (l', r') with
		      | _ -> Binary (n, o, l', r')
		  end
	  end
    | FuncCall (n, f, a) -> FuncCall(n, f, List.map fold_expr a)
    | Expression.If (n, c, t, f) ->
	let c' = fold_expr c
	and t' = fold_expr t
	and f' = fold_expr f
	in
	  begin
	    match c with
	      | Bool (_, true) -> t'
	      | Bool (_, false) -> f'
	      | _ -> Expression.If (n, c', t', f')
	  end
    | Label (n, e) -> Label (n, fold_expr e)
    | New (n, t, a) -> New (n, t, List.map fold_expr a)
    | Choose (n, v, t, p) -> Choose (n, v, t, fold_expr p)
    | Forall (n, v, t, p) ->
	let p' = fold_expr p in
	  begin
	    match p' with
		Bool(_, true) -> Bool(n, true)
	      | Bool(_, false) -> Bool(n, false)
	      | _ -> Forall (n, v, t, p')
	  end
    | Exists (n, v, t, p) ->
	let p' = fold_expr p in
	  begin
	    match p' with
		Bool(_, true) -> Bool(n, true)
	      | Bool(_, false) -> Bool(n, false)
	      | _ -> Exists (n, v, t, p')
	  end
    | Expression.Extern _ as e -> e
    | SSAId _ as e -> e
    | Phi (n, l) -> Phi (n, List.map fold_expr l)
  in
  let rec work =
    function
	Skip n -> Skip n
      | Assert (n, e) -> Assert (n, fold_expr e)
      | Prove (n, e) -> Prove (n, fold_expr e)
      | Assign (n, lhs, rhs) -> Assign (n, lhs, List.map fold_expr rhs)
      | Await (n, c) -> Await (n, fold_expr c)
      | Posit (n, c) -> Posit (n, fold_expr c)
      | Release n -> Release n
      | AsyncCall (n, l, c, m, s, a) ->
	  AsyncCall (n, l, c, m, s, List.map fold_expr a)
      | Reply (n, l, p) -> Reply (n, l, p)
      | Free (n, v) -> Free (n, v)
      | Bury (n, v) -> Bury (n, v)
      | SyncCall (n, c, m, s, i, o) ->
	  SyncCall (n, c, m, s, List.map fold_expr i, o)
      | AwaitSyncCall (n, c, m, s, i, o) ->
	  AwaitSyncCall (n, c, m, s, List.map fold_expr i, o)
      | LocalAsyncCall (n, l, m, s, ub, lb, i) ->
	  LocalAsyncCall (n, l, m, s, ub, lb, List.map fold_expr i)
      | LocalSyncCall (n, m, s, u, l, i, o) ->
	  LocalSyncCall (n, m, s, u, l, List.map fold_expr i, o)
      | AwaitLocalSyncCall (n, m, s, u, l, i, o) ->
	  AwaitLocalSyncCall (n, m, s, u, l, List.map fold_expr i, o)
      | Tailcall (n, m, s, u, l, i) ->
	  Tailcall (n, m, s, u, l, List.map fold_expr i)
      | If (n, c, l, r) -> If (n, fold_expr c, work l, work r)
      | While (n, c, i, b) -> While (n, c, fold_expr i, work b)
      | DoWhile (n, c, i, b) -> DoWhile (n, c, fold_expr i, b)
      | Sequence (n, s1, s2) -> Sequence (n, work s1, work s2)
      | Merge (n, s1, s2) -> Merge (n, work s1, work s2)
      | Choice (n, s1, s2) -> Choice (n, work s1, work s2)
      | Extern (n, s) -> Extern (n, s)
  in
    work stmt

let optimise_in_method program cls meth =
    match meth.Method.body with
	None ->
	  meth
      | Some body ->
	  let body' = optimise_in_statement meth body in
	    { meth with Method.body = Some body' }

let optimise program = Program.for_each_method program optimise_in_method
