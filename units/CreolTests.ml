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
    ] ;
    "Program" >::: [
      "class_provides" >::: [
        "simple" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    in
	    let program = [ Declaration.Class c ] in
	    let res = Program.class_provides program c in
	      assert_equal (Program.IdSet.singleton "Any") res
        ) ;
        "inherits" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ;
		      inherits = [ ("C", []) ]; contracts = []; implements = [];
		      attributes = []; with_defs = []; hidden = false;
		      file = ""; line = 0; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d ] in
	    let res = Program.class_provides program d in
	      assert_equal (Program.IdSet.singleton "Any") res
        ) ;
        "implements" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = [("I", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Interface i ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"]
	    in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
        ) ;
        "interface-inherits" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = [("J", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = [("I", [])];
		      with_decls = []; hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Interface i;
			    Declaration.Interface j ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"; "J" ]
	    in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
        ) ;
        "class-implements" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = [("I", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [("C", [])];
		      contracts = []; implements = [("J", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Interface i; Declaration.Interface j ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"]
	    in
	    let res = Program.class_provides program c in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
        ) ;
        "implements-class-inherits" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = []; implements = [("I", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [("C", [])];
		      contracts = []; implements = [("J", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Interface i; Declaration.Interface j ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "J"]
	    in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
        ) ;
        "contracts-implements" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = [("I", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [("C", [])];
		      contracts = []; implements = [("J", [])]; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Interface i; Declaration.Interface j ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"; "J"]
	    in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
        ) ;
        "contracts" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = [("I", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [("C", [])];
		      contracts = [("J", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Interface i; Declaration.Interface j ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"; "J"]
	    in
	    let res = Program.class_provides program d in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
	  ) ;
        "three-inherits" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = [("I", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [("C", [])];
		      contracts = [("J", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and e = { Class.name = "E"; parameters = [] ; inherits = [("D", [])];
		      contracts = [("K", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    and k = { Interface.name = "K"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Class e ; Declaration.Interface i;
			    Declaration.Interface j; Declaration.Interface k ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"; "J"; "K"]
	    in
	    let res = Program.class_provides program e in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
	  ) ;
        "inherit-two" >:: (
	  fun _ ->
	    let c = { Class.name = "C"; parameters = [] ; inherits = [];
		      contracts = [("I", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and d = { Class.name = "D"; parameters = [] ; inherits = [];
		      contracts = [("J", [])]; implements = []; attributes = [];
		      with_defs = []; hidden = false; file = ""; line = 0; }
	    and e = { Class.name = "E"; parameters = [] ;
		      inherits = [("C", []); ("D", [])]; contracts = [("K", [])];
		      implements = []; attributes = []; with_defs = [];
		      hidden = false; file = ""; line = 0; }
	    and i = { Interface.name = "I"; inherits = []; with_decls = [];
		      hidden = false; }
	    and j = { Interface.name = "J"; inherits = []; with_decls = [];
		      hidden = false; }
	    and k = { Interface.name = "K"; inherits = []; with_decls = [];
		      hidden = false; }
	    in
	    let program = [ Declaration.Class c ; Declaration.Class d;
			    Declaration.Class e ; Declaration.Interface i;
			    Declaration.Interface j; Declaration.Interface k ]
	    and expect =
	      List.fold_left (fun e a -> Program.IdSet.add a e)
	        Program.IdSet.empty ["Any"; "I"; "J"; "K"]
	    in
	    let res = Program.class_provides program e in
	      assert_bool "Sets differ" (Program.IdSet.equal expect res)
	  ) ;
      ] ;
    ] ;
  ]
