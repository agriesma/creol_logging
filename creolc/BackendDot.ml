(*
 * BackendDot.ml -- Generate graphs from creol programs.
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

(*s

*)

open Creol

let requires _ = []

let conflicts _ = []

type features = {
  classes: bool;
  objects: bool;
}

let emit ?(features={ classes = true; objects = true }) out_channel input =
  let c n = "C_" ^ n in
  let i n = "I_" ^ n in
  let d n = "D_" ^ n in
  let edge f t s =
    output_string out_channel (f ^ " -> " ^ t ^ "[style=" ^ s ^ "];\n") in
  let emit_node =
    function
        Declaration.Class { Class.name = n } when features.classes ->
  	    output_string out_channel
	      ((c n) ^ "[shape=box, label=\"" ^ n ^ "\"];\n")
      | Declaration.Interface { Interface.name = n } when features.classes ->
  	    output_string out_channel
	      ((i n) ^ "[shape=diamond, label=\"" ^ n ^ "\"];\n")
      | Declaration.Datatype { Datatype.name = t } when features.classes ->
  	    output_string out_channel
	      ((d (Type.name t)) ^ "[shape=ellipse, label=\"" ^
		 (Type.string_of_type t) ^ "\"];\n")
      | Declaration.Object { Object.name = n } when features.objects ->
  	    output_string out_channel
	      (n ^ "[shape=circle label=\"" ^ n ^ "\"];\n")
      | _ -> ()
  and emit_inherits =
    function
        Declaration.Class { Class.name = n; inherits = l } when features.classes ->
	  List.iter (fun t -> edge (c n) (c (Inherits.name t)) "solid") l
      | Declaration.Interface { Interface.name = n; inherits = [] } when features.classes ->
	  edge (i n) "I_Any" "solid"
      | Declaration.Interface { Interface.name = n; inherits = l } when features.classes ->
	  List.iter (fun t -> edge (i n) (i (Inherits.name t)) "solid") l
      | Declaration.Datatype { Datatype.name = n; supers = [] } when features.classes ->
	  edge (d (Type.name n)) "D_Data" "solid"
      | Declaration.Datatype { Datatype.name = n; supers = l } when features.classes ->
	  List.iter
	    (fun t -> edge (d (Type.name n)) (d (Type.name t)) "solid") l
      | _ -> ()
  and emit_implements =
    function
        Declaration.Class { Class.name = n; implements = l } when features.classes ->
	  List.iter (fun t -> edge (c n) (i (Inherits.name t)) "dashed") l
      | _ -> ()
  and emit_contracts =
    function
        Declaration.Class { Class.name = n; contracts = [] } when features.classes ->
	  edge (c n) "I_Any" "bold"
      | Declaration.Class { Class.name = n; contracts = l } when features.classes ->
	  List.iter (fun t -> edge (c n) (i (Inherits.name t)) "bold") l
      | _ -> ()
  and emit_links =
    function
        Declaration.Object { Object.name = n; attributes = a } when features.objects ->
	  let e f t s =
            output_string out_channel
              (f ^ " -> " ^ t ^ "[label=\"" ^ s ^ "\"];\n")
	  in
	  let f attr =
	    let rec get =
	      function
		| Expression.Tuple (_, l)
		| Expression.ListLit (_, l)
		| Expression.SetLit (_, l) -> List.flatten (List.map get l)
		| Expression.ObjLit (_, s) -> [s]
		| _ -> []
            in
            match attr with
	      | { VarDecl.name = l ; init = Some i } ->
		List.iter (fun t -> e n t l) (get i)
              | _ -> ()
          in
	    List.iter f a
      | _ -> ()
  in
  output_string out_channel "digraph G {\n" ;
  Program.iter input emit_node ;
  Program.iter input emit_inherits ;
  Program.iter input emit_implements ;
  Program.iter input emit_contracts ;
  Program.iter input emit_links ;
  output_string out_channel "}\n"
