(*
 * CreolTests.ml -- Unit Tests for the Creol module and its sub-module.
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

open OUnit
open Creol

let set_of_list lst =
  List.fold_left (fun e a -> IdSet.add a e) IdSet.empty lst

let conv_inh (n, a) = { Inherits.name = n; arguments = a }

let make_class name ?(contracts=[]) ?(implements=[]) inherits =
  { Class.name = name; parameters = [] ;
    inherits = List.map conv_inh inherits;
    contracts = List.map conv_inh contracts;
    implements = List.map conv_inh implements;
    attributes = []; with_defs = []; pragmas = []; file = ""; line = 0 }

let make_iface name inherits =
  { Interface.name = name;
    inherits = List.map conv_inh inherits;
    with_decls = []; pragmas = [] }

let test_fixture = "Creol" >:::
  [
    "Type" >::: [
      "Any" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Any' wrong" Type.any (Type.Basic "Any") ;
	  assert_bool "Any is not of type `Any'" (Type.any_p Type.any)
      ) ;
      "Data" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Data' wrong" Type.data (Type.Basic "Data") ;
	  assert_bool "Any is not of type `Data'" (Type.data_p Type.data)
      ) ;
      "Bool" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Bool' wrong" Type.bool (Type.Basic "Bool") ;
	  assert_bool "Any is not of type `Bool'" (Type.bool_p Type.bool)
      ) ;
      "Int" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Int' wrong" Type.int (Type.Basic "Int") ;
	  assert_bool "Any is not of type `Int'" (Type.int_p Type.int)
      ) ;
      "Float" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Float' wrong" Type.float (Type.Basic "Float") ;
	  assert_bool "Any is not of type `Float'" (Type.float_p Type.float)
      ) ;
      "String" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `String' wrong" Type.string (Type.Basic "String") ;
	  assert_bool "Any is not of type `String'" (Type.string_p Type.string)
      ) ;
      "Time" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Time' wrong" Type.time (Type.Basic "Time") ;
	  assert_bool "Any is not of type `Time'" (Type.time_p Type.time)
      ) ;
      "Time" >:: (
        fun _ ->
          assert_equal ~msg:"Constant for type `Time' wrong" Type.time (Type.Basic "Time") ;
	  assert_bool "Any is not of type `Time'" (Type.time_p Type.time)
      ) ;
      "normalise" >::: [
        "empty" >:: (
	  fun _ ->
	    let s = IdMap.empty in
	    let res = Type.normalise s in
	      assert_bool "Map not empty." (IdMap.is_empty res)
	) ;
        "none" >:: (
	  fun _ ->
	    let s = IdMap.add "b" Type.string (IdMap.add "a" Type.int IdMap.empty) in
	    let res = Type.normalise s in
	      assert_equal ~msg:"Maps differ." s res
	) ;
        "vars" >:: (
	  fun _ ->
	    let s = IdMap.add "a" (Type.Variable "b") IdMap.empty in
	    let exp = IdMap.add "a" (Type.Variable "b") IdMap.empty in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
        "simple" >:: (
	  fun _ ->
	    let s = IdMap.add "b" Type.int (IdMap.add "a" (Type.Variable "b") IdMap.empty) in
	    let exp = IdMap.add "b" Type.int (IdMap.add "a" Type.int IdMap.empty) in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
        "deep" >:: (
	  fun _ ->
	    let s = IdMap.add "c" Type.int
                      (IdMap.add "b" (Type.Variable "c") 
                        (IdMap.add "a" (Type.Variable "b") IdMap.empty)) in
	    let exp = IdMap.add "c" Type.int
                      (IdMap.add "b" Type.int 
                        (IdMap.add "a" Type.int IdMap.empty)) in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
        "cycle" >:: (
	  fun _ ->
	    let s = IdMap.add "b" (Type.Variable "a") (IdMap.add "a" (Type.Variable "b") IdMap.empty) in
	    let exp = IdMap.add "b" (Type.Variable "b") (IdMap.add "a" (Type.Variable "a") IdMap.empty) in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
        "deep-cycle" >:: (
	  fun _ ->
	    let s = IdMap.add "c" (Type.Variable "a") (IdMap.add "b" (Type.Variable "c") (IdMap.add "a" (Type.Variable "b") IdMap.empty)) in
	    let exp = IdMap.add "c" (Type.Variable "c") (IdMap.add "b" (Type.Variable "b") (IdMap.add "a" (Type.Variable "a") IdMap.empty)) in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
        "complex-cycle" >:: (
	  fun _ ->
	    let s = IdMap.add "a" (Type.Application ("List", [Type.Variable "b"]))
                      (IdMap.add "b" (Type.Application ("List", [Type.Variable "b"])) IdMap.empty) in
	    let exp = IdMap.add "a" (Type.Application ("List", [Type.Variable "b"]))
                      (IdMap.add "b" (Type.Application ("List", [Type.Variable "b"])) IdMap.empty) in
	    let res = Type.normalise s in
	      assert_equal ~msg:("Maps differ: " ^ (Type.string_of_substitution res)) exp res
	) ;
      ] ;
    ] ;
    "Program" >::: [
      "diamonds" >::: [
        "simple" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    in
	    let program = Program.make [ Declaration.Class c ] in
	    let res = Program.diamonds program c.Class.name in
	      assert_equal IdSet.empty res
        ) ;
        "single-inherits" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" [("C", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d ] in
	    let res = Program.diamonds program d.Class.name in
	      assert_equal IdSet.empty res
        ) ;
        "double-inherits" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" [("C", []); ("C", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d ] in
	    let res = Program.diamonds program d.Class.name in
	      assert_equal (IdSet.singleton "C") res
        ) ;
        "inherits-two" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" []
	    and e = make_class "E" [("C", []); ("D", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
			    Declaration.Class e ] in
	    let res = Program.diamonds program e.Class.name in
	      assert_equal IdSet.empty res
	) ;
        "inherits-tree" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" []
	    and e = make_class "E" [("C", [])]
	    and f = make_class "F" [("D", []); ("E", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e;
					 Declaration.Class f ] in
	    let res = Program.diamonds program f.Class.name in
	      assert_equal IdSet.empty res
	) ;
        "inherits-diamond" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" [("C", [])]
	    and e = make_class "E" [("C", [])]
	    and f = make_class "F" [("D", []); ("E", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e;
					 Declaration.Class f ] in
	    let res = Program.diamonds program f.Class.name in
	      assert_equal (IdSet.singleton "C") res
	) ;
        "inherits-late-diamond" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" []
	    and e = make_class "E" [("C", [])]
	    and f = make_class "F" [("C", [])]
	    and g = make_class "G" [("D", []); ("E", []); ("F", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e;
					 Declaration.Class f;
					 Declaration.Class g ] in
	    let res = Program.diamonds program g.Class.name in
	      assert_equal (IdSet.singleton "C") res
	) ;
        "inherits-dumb-diamond" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" [("C", [])]
	    and e = make_class "E" [("C", []); ("D", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e] in
	    let res = Program.diamonds program e.Class.name in
	      assert_equal (IdSet.singleton "C") res
	) ;
      ] ;
      "class_provides" >::: [
        "simple" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    in
	    let program = Program.make [ Declaration.Class c ] in
	    let res = Program.class_provides program c in
	      assert_equal (IdSet.singleton "Any") res
        ) ;
        "inherits" >:: (
	  fun _ ->
	    let c = make_class "C" []
	    and d = make_class "D" [("C", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d ] in
	    let res = Program.class_provides program d in
	      assert_equal (IdSet.singleton "Any") res
        ) ;
        "implements" >:: (
	  fun _ ->
	    let c = make_class "C" ~implements:[("I", [])] []
	    and i = make_iface "I" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Interface i ]
	    and expect = set_of_list ["Any"; "I"] in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (IdSet.equal expect res)
        ) ;
        "interface-inherits" >:: (
	  fun _ ->
	    let c = make_class "C" ~implements:[("J", [])] []
	    and i = make_iface "I" []
	    and j = make_iface "J"  [("I", [])]
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Interface i;
					 Declaration.Interface j ]
	    and expect = set_of_list ["Any"; "I"; "J" ] in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (IdSet.equal expect res)
        ) ;
        "class-implements" >:: (
	  fun _ ->
	    let c = make_class "C" ~implements:[("I", [])] []
	    and d = make_class "D" ~implements:[("J", [])] [("C", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Interface i;
					 Declaration.Interface j ]
	    and expect = set_of_list ["Any"; "I"] in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (IdSet.equal expect res)
        ) ;
        "implements-class-inherits" >:: (
	  fun _ ->
	    let c = make_class "C" [] ~implements:[("I", [])]
	    and d = make_class "D" [("C", [])] ~implements:[("J", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Interface i;
					 Declaration.Interface j ]
	    and expect = set_of_list ["Any"; "J"] in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (IdSet.equal expect res)
        ) ;
        "contracts-implements" >:: (
	  fun _ ->
	    let c = make_class "C" [] ~contracts:[("I", [])]
	    and d = make_class "D" [("C", [])] ~implements:[("J", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Interface i;
					 Declaration.Interface j ]
	    and expect = set_of_list ["Any"; "I"; "J"] in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (IdSet.equal expect res)
        ) ;
        "contracts" >:: (
	  fun _ ->
	    let c = make_class "C" [] ~contracts:[("I", [])]
	    and d = make_class "D" [("C", [])] ~contracts:[("J", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Interface i;
					 Declaration.Interface j ]
	    and expect = set_of_list ["Any"; "I"; "J"] in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (IdSet.equal expect res)
	  ) ;
        "three-inherits" >:: (
	  fun _ ->
	    let c = make_class "C" [] ~contracts:[("I", [])]
	    and d = make_class "D" [("C", [])] ~contracts:[("J", [])]
	    and e = make_class "E" [("D", [])] ~contracts:[("K", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    and k = make_iface "K" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e;
					 Declaration.Interface i;
					 Declaration.Interface j;
					 Declaration.Interface k ]
	    and expect = set_of_list ["Any"; "I"; "J"; "K"] in
	    let res = Program.class_provides program e in
	      assert_bool "Sets differ" (IdSet.equal expect res)
	  ) ;
        "inherit-two" >:: (
	  fun _ ->
	    let c = make_class "C" [] ~contracts:[("I", [])]
	    and d = make_class "D" [] ~contracts:[("J", [])]
	    and e = make_class "E" [("C", []); ("D", [])] ~contracts:[("K", [])]
	    and i = make_iface "I" []
	    and j = make_iface "J" []
	    and k = make_iface "K" []
	    in
	    let program = Program.make [ Declaration.Class c;
					 Declaration.Class d;
					 Declaration.Class e;
					 Declaration.Interface i;
					 Declaration.Interface j;
					 Declaration.Interface k ]
	    and expect = set_of_list ["Any"; "I"; "J"; "K"] in
	    let res = Program.class_provides program e in
	      assert_bool "Sets differ" (IdSet.equal expect res)
	  ) ;
      ] ;
      "cycles" >::: [
        "classes" >:: (
	  fun _ -> 
	    let a = make_class "A" [("C", [])]
	    and b = make_class "B" [("A", [])]
	    and c = make_class "C" [("B", [])] in
	    let tree = Program.make [ Declaration.Class a;
				      Declaration.Class b;
				      Declaration.Class c ] in
	    let rel = Program.transitive_closure (Program.class_hierarchy tree)
	    in
	    let res = Program.acyclic_p rel in
	      assert_bool "No cycle." (not res)
        );
        "interfaces" >:: (
	  fun _ -> 
	    let a = make_iface "A" [("C", [])]
	    and b = make_iface "B" [("A", [])]
	    and c = make_iface "C" [("B", [])] in
	    let tree = Program.make [ Declaration.Interface a;
				      Declaration.Interface b;
				      Declaration.Interface c ] in
	    let rel = Program.transitive_closure (Program.subtype_relation tree)
	    in
	    let res = Program.acyclic_p rel in
	      assert_bool "No cycle." (not res)
        );
      ] ;
    ] ;
  ]
