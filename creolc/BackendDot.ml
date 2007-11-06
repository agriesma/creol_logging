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

let emit out_channel input =
  let c n = "C_" ^ n in
  let i n = "I_" ^ n in
  let d n = "D_" ^ n in
  let edge f t s =
    output_string out_channel (f ^ " -> " ^ t ^ "[style=" ^ s ^ "];\n") in
  let emit_node =
    function
        Declaration.Class { Class.name = n } ->
  	    output_string out_channel ((c n) ^ "[shape=box, label=\"" ^ n ^ "\"];\n")
      | Declaration.Interface { Interface.name = n } ->
  	    output_string out_channel ((i n) ^ "[shape=diamond, label=\"" ^ n ^ "\"];\n")
      | Declaration.Datatype { Datatype.name = t } ->
  	    output_string out_channel ((d (Type.name t)) ^ "[shape=ellipse, label=\"" ^ (Type.as_string t) ^ "\"];\n")
      | _ -> ()
  and emit_inherits =
    function
        Declaration.Class { Class.name = n; inherits = l } ->
	  List.iter (fun t -> edge (c n) (c (fst t)) "solid") l
      | Declaration.Interface { Interface.name = n; inherits = [] } ->
	  edge (i n) "I_Any" "solid"
      | Declaration.Interface { Interface.name = n; inherits = l } ->
	  List.iter (fun t -> edge (i n) (i (fst t)) "solid") l
      | Declaration.Datatype { Datatype.name = n; supers = [] } ->
	  edge (d (Type.name n)) "D_Data" "solid"
      | Declaration.Datatype { Datatype.name = n; supers = l } ->
	  List.iter (fun t -> edge (d (Type.name n)) (d (Type.name t)) "solid") l
      | _ -> ()
  and emit_implements =
    function
        Declaration.Class { Class.name = n; implements = l } ->
	  List.iter (fun t -> edge (c n) (i (fst t)) "dashed") l
      | _ -> ()
  and emit_contracts =
    function
        Declaration.Class { Class.name = n; contracts = [] } ->
	  edge (c n) "I_Any" "bold"
      | Declaration.Class { Class.name = n; contracts = l } ->
	  List.iter (fun t -> edge (c n) (i (fst t)) "bold") l
      | _ -> ()
  in
  output_string out_channel "digraph G {\n" ;
  List.iter emit_node input ;
  List.iter emit_inherits input ;
  List.iter emit_implements input ;
  List.iter emit_contracts input ;
  output_string out_channel "}\n"
