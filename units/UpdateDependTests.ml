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


(** Get the update terms from the result of UpdateDepend.depend *)
let depend program update =
  let result = UpdateDepend.depend program update in
    match result.Program.decls with
      | [ Declaration.NewClass { NewClass.dependencies = res} ] -> res
      | [ Declaration.Update { Update.dependencies = res} ] -> res
      | _ -> assert false

let c0 =
  { Class.name = "C"; parameters = [] ; inherits = []; contracts = [];
    implements = []; attributes = []; invariants = []; with_defs = [];
    objects_created = Big_int.zero_big_int; pragmas = []; file = ""; line = 0 }

let c1 =
  { Class.name = "C"; parameters = [] ; inherits = []; contracts = [];
    implements = [];
    attributes = [{ VarDecl.name = "a"; var_type = Type.data; init = None;
                    file = ""; line = 0 }];
    invariants = []; with_defs = []; objects_created = Big_int.zero_big_int;
    pragmas = [{ Pragma.name = "Version";
                 values = [Expression.Int (Expression.make_note(),
                                           Big_int.unit_big_int)]}];
                 file = ""; line = 0 }

let d1 =
  { Class.name = "D"; parameters = [] ;
    inherits = [{ Inherits.name = "C"; arguments = []; file = ""; line = 0}];
    contracts = []; objects_created = Big_int.zero_big_int;
    implements = []; attributes = []; invariants = []; with_defs = [];
    pragmas = [{ Pragma.name = "Version";
                 values = [Expression.Int (Expression.make_note(),
                                           Big_int.unit_big_int)]}];
                 file = ""; line = 0 }

let upd0 =
  { Update.name = "C"; inherits = []; contracts = []; implements = [];
    attributes = []; with_defs = []; pragmas = [];
    dependencies = Dependencies.empty }

let upd1 =
  { Update.name = "D"; inherits = []; contracts = []; implements = [];
    attributes = []; with_defs = []; pragmas = [];
    dependencies = Dependencies.empty }

let upd2 =
  { Update.name = "D"; inherits = []; contracts = []; implements = [];
    attributes = [];
    with_defs = [{ With.co_interface = Type.any;
                   methods = [{ Method.name = "m";
                                coiface = Type.any;
                                inpars = []; outpars = [];
                                requires = Expression.Bool (Expression.make_note (), true);
                                ensures = Expression.Bool (Expression.make_note (), true);
                                vars = [];
                                body = Some (Statement.Assign (Statement.make_note (),
                                             [Expression.LhsId (Expression.make_note (), "a")],
                                             [Expression.Bool (Expression.make_note (), true)]));
                                location = ""; file = ""; line = 0 }];
                   invariants = []; file = ""; line = 0 }];
    pragmas = [];
    dependencies = Dependencies.empty }

let test_fixture = "UpdateDepend" >:::
  [
    "new0" >:: (
      fun _ ->
        let program = Program.make []
        and update = Program.make [ Declaration.NewClass { NewClass.cls = c0; dependencies = Dependencies.empty } ]
        and expect = Dependencies.empty
        in
        let result = depend program update in
          assert_bool "Dependencies differ" (Dependencies.equal expect result)
    );
    "simple0" >:: (
      fun _ ->
        let program = Program.make [Declaration.Class c0]
        and update = Program.make [Declaration.Update upd0]
        and expect = Dependencies.singleton { Dependency.name = "C"; version = Big_int.zero_big_int }
        in
        let result = depend program update in
          assert_bool "Dependencies differ" (Dependencies.equal expect result)
    );
    "simple1" >:: (
      fun _ ->
        let program = Program.make [Declaration.Class c1]
        and update = Program.make [Declaration.Update upd0]
        and expect = Dependencies.singleton { Dependency.name = "C"; version = Big_int.unit_big_int }
        in
        let result = depend program update in
          assert_bool "Dependencies differ" (Dependencies.equal expect result)
    );
    "simple2" >:: (
      fun _ ->
        let program = Program.make [Declaration.Class c1; Declaration.Class d1]
        and update = Program.make [Declaration.Update upd1]
        and expect = Dependencies.singleton { Dependency.name = "D"; version = Big_int.unit_big_int }
        in
        let result = depend program update in
          assert_bool "Dependencies differ" (Dependencies.equal expect result)
    );
    "simple3" >:: (
      fun _ ->
        let program = Program.make [Declaration.Class c1; Declaration.Class d1]
        and update = Program.make [Declaration.Update upd2]
        and expect = Dependencies.add
          { Dependency.name = "C"; version = Big_int.unit_big_int }
          (Dependencies.singleton { Dependency.name = "D"; version = Big_int.unit_big_int })
        in
        let result = depend program update in
          assert_bool "Dependencies differ" (Dependencies.equal expect result)
    );
  ]
