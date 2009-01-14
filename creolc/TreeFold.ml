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

(* The passes which must have been executed before using any of the
   functions defined in this module. *)

let dependencies = "typecheck"

let log l = Messages.message (l + 1)
let is_zero = Big_int.eq_big_int Big_int.zero_big_int
let is_one = Big_int.eq_big_int Big_int.unit_big_int
let is_one_num = Num.eq_num (Num.num_of_int 1)

let zero_float_p f =
  match classify_float f with
      FP_zero -> true
    | _ -> false

let one_float_p f = (abs_float (f -. 1.0)) < epsilon_float

(* This function tries to fold all constant expressions to literals.

   The current implementation has some limitation:
   \begin{itemize}
   \item Numbers are computed as OCaml integers (30 bits on 32 bit
     platforms and 62 bits on 64 bit platforms).  Overflows are
     unhandled.  This may lead to incorrect compiler output.
   \item Associativity and commutativity is not handled yet.  The
     expression $1+x+1$ is neither folded to $2+x$ nor $x+2$.
   \end{itemize} *)

let optimise_in_statement stmt =
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
    | MapLit (n, l) ->
	MapLit (n, List.map (fun (d, r) -> (fold_expr d, fold_expr r)) l)
    | FuncCall (n, o, [e]) ->
        let e' = fold_expr e in
          begin
            match o with
              | "~" ->
                  begin
		    match e' with
                      | Bool(_, true) -> Bool(n, false)
                      | Bool(_, false) -> Bool(n, true)
                      | FuncCall (n', "~", [e'']) -> Expression.set_note n e''
                      | _ -> FuncCall (n, o, [e'])
                  end
              | "-" ->
                  begin
                    match e' with
                      | Int (_, v) when is_zero v -> Int (n, v)
                      | Float (_, v) when zero_float_p v -> Float (n, v)
                      | FuncCall (n'', "-", [e'']) -> Expression.set_note n e''
                      | _ -> FuncCall (n, o, [e'])
                  end
              | "#" ->
                  begin
                    match e' with
                      | Nil _ -> Int (n, Big_int.zero_big_int)
                      | ListLit (_, l) ->
                          Int (n, Big_int.big_int_of_int (List.length l))
                      | SetLit (_, []) -> Int (n, Big_int.zero_big_int)
                      | _ -> FuncCall (n, o, [e'])
                  end
	      | _ -> FuncCall (n, o, [e'])
          end
    | FuncCall (n, o, [l; r]) ->
	let l' = fold_expr l
	and r' = fold_expr r
	in
	  begin
	    match o with
		"+" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), _) when is_zero lv -> r'
                      | (_, Int (_, rv)) when is_zero rv -> l'
		      | (Int (_, lv), Int (_, rv)) ->
                          Int (n, Big_int.add_big_int lv rv)
		      | (Float (_, lv), _) when zero_float_p lv -> r'
                      | (_, Float (_, rv)) when zero_float_p rv -> l'
		      | (Float (_, lv), Float (_, rv)) ->
                          Float (n, lv +. rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "-" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), _) when  is_zero lv -> r'
                      | (_, Int (_, rv)) when is_zero rv -> l'
		      | (Int (_, lv), Int (_, rv)) ->
                          Int (n, Big_int.sub_big_int lv rv)
		      | (Float (_, lv), _) when  zero_float_p lv -> r'
                      | (_, Float (_, rv)) when zero_float_p rv -> l'
		      | (Float (_, lv), Float (_, rv)) ->
                          Float (n, lv -. rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "*" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), _) when is_one lv -> r'
                      | (_, Int (_, rv)) when is_one rv -> l'
		      | (Int (_, lv), _) when is_zero lv -> l'
                      | (_, Int (_, rv)) when is_zero rv -> r'
		      | (Int (_, lv), Int (_, rv)) ->
			  Int (n, Big_int.mult_big_int lv rv)
		      | (Float (_, lv), _) when one_float_p lv -> r'
                      | (_, Float (_, rv)) when one_float_p rv -> l'
		      | (Float (_, lv), _) when zero_float_p lv -> l'
                      | (_, Float (_, rv)) when zero_float_p rv -> r'
		      | (Float (_, lv), Float (_, rv)) ->
			  Float (n, lv *. rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "/" ->
		  begin
		    match (l', r') with
                      | (_, Int (_, rv)) when is_one rv -> l'
		      | (Int (_, lv), _) when is_zero lv -> l'
                      | (_, Int (_, rv)) when is_zero rv ->
			  assert false; (* Report division by zero? *)
		      |	(Int (_, lv), Int (_, rv)) ->
                          Int (n, Big_int.div_big_int lv rv)
                      | (_, Float (_, rv)) when one_float_p rv -> l'
		      | (Float (_, lv), _) when zero_float_p lv -> l'
                      | (_, Float (_, rv)) when zero_float_p rv ->
			  assert false; (* Report division by zero? *)
		      |	(Float (_, lv), Float (_, rv)) ->
                          Float (n, lv /. rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "%" ->
		  begin
		    match (l', r') with
                      | (_, Int (_, rv)) when is_one rv -> l'
		      | (Int (_, lv), _) when is_zero lv -> l'
                      | (_, Int (_, rv)) when is_zero rv ->
			  assert false; (* Report division by zero? *)
		      | (Int (_, lv), Int (_, rv)) ->
                          Int (n, Big_int.mod_big_int lv rv)
                      | (_, Float (_, rv)) when zero_float_p rv -> l'
		      | (Float (_, lv), _) when one_float_p lv -> l'
                      | (_, Float (_, rv)) when zero_float_p rv ->
			  assert false; (* Report division by zero? *)
		      | (Float (_, lv), Float (_, rv)) ->
                          Float (n, mod_float lv rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "**" ->
		  begin
		    match (l', r') with
                      | (Int (_, lv), _) when is_one lv -> l'
                      | (_, Int (_, rv)) when is_one rv -> l'
		      | (Int (_, lv), _) when is_zero lv -> l'
                      | (_, Int (_, rv)) when is_zero rv ->
			  Int (n, Big_int.zero_big_int)
		      | (Int (_, lv), Int (_, rv)) ->
                          Int (n, Big_int.power_big_int_positive_big_int lv rv)
                      | (Float (_, lv), _) when one_float_p lv -> l'
                      | (_, Float (_, rv)) when one_float_p rv -> l'
		      | (Float (_, lv), _) when zero_float_p lv -> l'
                      | (_, Float (_, rv)) when zero_float_p rv ->
			  Float (n, 1.0)
		      | (Float (_, lv), Float (_, rv)) ->
                          Float (n, lv ** rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "="  ->
		  if l' = r' then
		    Bool (n, true)
		  else
		    FuncCall (n, o, [l'; r'])
	      | "/="  ->
		  if l' = r' then
		    Bool (n, false)
		  else
		    FuncCall (n, o, [l'; r'])
	      | "<=" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), Int (_, rv)) ->
			  Bool (n, Big_int.le_big_int lv rv)
		      | (Int (_, lv), Float (_, rv)) ->
			  Bool (n, (Big_int.float_of_big_int lv) <= rv)
		      | (Float (_, lv), Int (_, rv)) ->
			  Bool (n, lv <= (Big_int.float_of_big_int rv))
		      | (Float (_, lv), Float (_, rv)) ->
			  Bool (n, lv <= rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "<" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), Int (_, rv)) ->
			  Bool (n, Big_int.lt_big_int lv rv)
		      | (Int (_, lv), Float (_, rv)) ->
			  Bool (n, (Big_int.float_of_big_int lv) < rv)
		      | (Float (_, lv), Int (_, rv)) ->
			  Bool (n, lv < (Big_int.float_of_big_int rv))
		      | (Float (_, lv), Float (_, rv)) ->
			  Bool (n, lv < rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | ">=" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), Int (_, rv)) ->
			  Bool (n, Big_int.ge_big_int lv rv)
		      | (Int (_, lv), Float (_, rv)) ->
			  Bool (n, (Big_int.float_of_big_int lv) >= rv)
		      | (Float (_, lv), Int (_, rv)) ->
			  Bool (n, lv >= (Big_int.float_of_big_int rv))
		      | (Float (_, lv), Float (_, rv)) ->
			  Bool (n, lv >= rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | ">" ->
		  begin
		    match (l', r') with
		      | (Int (_, lv), Int (_, rv)) ->
			  Bool (n, Big_int.gt_big_int lv rv)
		      | (Int (_, lv), Float (_, rv)) ->
			  Bool (n, (Big_int.float_of_big_int lv) > rv)
		      | (Float (_, lv), Int (_, rv)) ->
			  Bool (n, lv > (Big_int.float_of_big_int rv))
		      | (Float (_, lv), Float (_, rv)) ->
			  Bool (n, lv > rv)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "&&"  ->
		  begin
		    match (l', r') with
		      | (Bool (_, false), _) -> Bool (n, false)
		      | (_, Bool (_, false)) -> Bool (n, false)
		      | (Bool(_, true), Bool (_, true)) -> Bool (n, true)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "/\\" ->
		  begin
		    match (l', r') with
		      | (Bool (_, false), _) -> Bool (n, false)
		      | (_, Bool (_, false)) -> Bool (n, false)
		      | (Bool(_, true), Bool (_, true)) -> Bool (n, true)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "||" ->
		  begin
		    match (l', r') with
		      | (Bool (_, true), _) -> Bool (n, true)
		      | (_, Bool (_, true)) -> Bool (n, true)
		      | (Bool(_, false), Bool (_, false)) -> Bool (n, false)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "\\/" ->
		  begin
		    match (l', r') with
		      | (Bool (_, true), _) -> Bool (n, true)
		      | (_, Bool (_, true)) -> Bool (n, true)
		      | (Bool(_, false), Bool (_, false)) -> Bool (n, false)
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "^" ->
		  if l' = r' then
		    Bool (n, false)
		  else
		    FuncCall (n, o, [l'; r'])
	      | "=>" ->
		  begin
		    match (l', r') with
		      | (Bool (_, false), _) -> Bool (n, true)
		      | (_, Bool (_, false)) ->
			  fold_expr (FuncCall (n, "~", [l']))
		      | (Bool (_, true), _) -> Expression.set_note n r'
		      | (_, Bool (_, true)) -> Expression.set_note n l'
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "<=>" ->
		  if l' = r' then
		    Bool (n, true)
		  else
		    FuncCall (n, o, [l'; r'])
	      | "-|" ->
		  begin
		    match (l', r') with
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "|-" ->
		  begin
		    match (l', r') with
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "|-|" ->
		  begin
		    match (l', r') with
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "\\" ->
		  begin
		    match (l', r') with
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | "in" ->
		  begin
		    match (l', r') with
		      | _ -> FuncCall (n, o, [l'; r'])
		  end
	      | _ ->
	          FuncCall(n, o, [l'; r'])
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
    | ObjLit _ as e -> e
    | LabelLit (n, l) -> LabelLit (n, List.map fold_expr l)
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
      | Get (n, l, p) -> Get (n, l, p)
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
      | MultiCast (a, c, m, s, i) ->
	  MultiCast (a, fold_expr c, m, s, List.map fold_expr i)
      | Tailcall (n, c, m, s, i) ->
	  Tailcall (n, fold_expr c, m, s, List.map fold_expr i)
      | StaticTail (n, m, s, u, l, i) ->
	  StaticTail (n, m, s, u, l, List.map fold_expr i)
      | If (n, c, l, r) -> If (n, fold_expr c, work l, work r)
      | While (n, c, i, b) -> While (n, c, fold_expr i, work b)
      | DoWhile (n, c, i, b) -> DoWhile (n, c, fold_expr i, b)
      | Sequence (n, s1, s2) -> Sequence (n, work s1, work s2)
      | Merge (n, s1, s2) -> Merge (n, work s1, work s2)
      | Choice (n, s1, s2) -> Choice (n, work s1, work s2)
      | Return (n, r) -> Return (n, List.map fold_expr r)
      | Continue (n, c) -> Continue (n, fold_expr c)
      | Extern (n, s) -> Extern (n, s)
  in
    work stmt

let optimise_in_method program cls meth =
  Method.apply_to_body optimise_in_statement meth

let optimise program = Program.for_each_method program optimise_in_method
