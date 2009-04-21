(* The grammar of Creol Updates.

   This is the input file is for use with the Menhir parser generator.
 *)

%{

(*
 * UpdateParser.mly -- A parser for Creol updates.
 *
 * This file is part of creoltools.
 *
 * Copyright (c) 2007, 2008, 2009 by Marcel Kyas
 *
 * The code in CreolCreolParser.mly has been generated by the menhir parser
 * generator.  In accordance with the Lesser General Public License,
 * the generated parser as well as its source file are distributed
 * under the terms of the GPL:
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
i*)

open Lexing
open Creol
open Expression
open Statement
open Method
open VarDecl

exception Error

(*
Print a short error message and abort
*)
let signal_error s m = Messages.error s.pos_fname s.pos_lnum m; exit 1

(*
A \ocwlowerid{super\_decl} is used to allow a more relaxed parsing
of contracts, implements, and inherits clauses.  The grammar allows
that these clauses occur in any order and even multiple times.  When
building the representation of a class or interface, these
\ocwlowerid{super\_decl} trees are recollected into single lists.
*)
type super_decl =
    Contracts of Inherits.t list
  | Implements of Inherits.t list
  | Inherits of Inherits.t list

let contracts l =
  List.flatten
    (List.fold_left (fun a -> function Contracts m -> m::a | _ -> a) [] l)

let implements l =
  List.flatten
    (List.fold_left (fun a -> function Implements m -> m::a | _ -> a) [] l)

let inherits l =
  List.flatten
    (List.fold_left (fun a -> function Inherits m -> m::a | _ -> a) [] l)

let upd_method_locs n w =
  List.map (fun x -> { x with With.methods =
      List.map (fun y -> { y with Method.location = n }) x.With.methods }) w

(* Make a new expression note from the lexical position. *)
let expression_note pos =
  Expression.make_note ~file:pos.pos_fname ~line:pos.pos_lnum ()

(* Make a new statement note from the lexical position. *)
let statement_note pos =
  Statement.make_note ~file:pos.pos_fname ~line:pos.pos_lnum ()

%}

%start <Creol.Declaration.t list> main

%%

main:
      d = list(declaration) EOF { d }

declaration:
      NEW d = interfacedecl { Declaration.Interface d }
    | NEW d = classdecl
       { Declaration.NewClass { NewClass.cls = d;
                                dependencies = Dependencies.empty } }
    | d = updatedecl { Declaration.Update d }
    | d = retractdecl { Declaration.Retract d }
    | error { signal_error $startpos "syntax error" }

updatedecl:
      UPDATE n = CID s = list(super_decl) pr = list(pragma)
      BEGIN
        a = list(terminated(attribute, ioption(SEMI))) i = list(invariant)
        aw = loption(anon_with_def) w = list(with_def)
      END
    { { Update.name = n; inherits = inherits s; contracts = contracts s;
        implements = implements s; attributes = List.flatten a;
        with_defs = upd_method_locs n (aw @ w); pragmas = pr;
        dependencies = Dependencies.empty;
        file = $startpos.pos_fname; line = $startpos.pos_lnum } }

retractdecl:
      RETRACT n = CID s = list(super_decl) pr = list(pragma)
      BEGIN
        a = list(terminated(attribute, ioption(SEMI))) i = list(invariant)
        aw = loption(anon_with_decl) w = list(with_decl)
      END
    { let _ = assert ([] = contracts s); assert ([] = implements s)
      in
        { Retract.name = n; inherits = inherits s; attributes = List.flatten a;
          with_defs = upd_method_locs n (aw @ w); pragmas = pr;
          dependencies = Dependencies.empty; obj_deps = Dependencies.empty;
          file = $startpos.pos_fname; line = $startpos.pos_lnum } }

anon_with_decl:
      l = nonempty_list(method_decl) i = list(invariant)
        { [ { With.co_interface = Type.Internal;
              methods = List.map (Method.set_cointerface Type.Internal) l;
              invariants = i;
              file  = $startpos.pos_fname; line = $startpos.pos_lnum } ] }

%%
(* The trailer is currently empty *)
