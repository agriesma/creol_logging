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
    ]
  ]
