(*
 * UpdateDepend.ml -- Calculate dependencies of an update.
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

let dependencies = ""

let log l = Messages.message (l + 1)


let rec depend_expression program cls meth =
  function
    | This _ | QualifiedThis _ | Caller _ | Now _ | Null _ | Nil _ | History _
    | Bool _ | Int _ | Float _ | String _ -> Dependencies.empty
    | Id (_, n) ->
        begin
          try
            let _ = Method.find_variable meth n in Dependencies.empty
          with Not_found ->
            let cls' = Program.find_class_of_attr program cls n in
              Dependencies.singleton { Dependency.name = cls'.Class.name;
                                       version = Class.version cls' }
        end
    | StaticAttr (_, n, (Type.Basic c)) ->
        let c' = Program.find_class program c in
        let cls' = Program.find_class_of_attr program c' n in
          Dependencies.singleton { Dependency.name = cls'.Class.name;
                                   version = Class.version cls' }
    | Tuple (_, l) | ListLit (_, l) | SetLit (_, l) | FuncCall (_, _, l) ->
        List.fold_left Dependencies.union Dependencies.empty
          (List.map (depend_expression program cls meth) l)
    | MapLit (_, l) ->
        let f (d, r) =
          let d' = depend_expression program cls meth d 
          and r' = depend_expression program cls meth r
          in
            Dependencies.union d' r'
        in
	  List.fold_left Dependencies.union Dependencies.empty (List.map f l)
    | Expression.If (_, c, t, f) ->
	let c' = depend_expression program cls meth c
	and t' = depend_expression program cls meth t
	and f' = depend_expression program cls meth f
	in
          Dependencies.union c' (Dependencies.union t' f')
    | Label (_, e) -> depend_expression program cls meth e
    | New (_, (Type.Basic c), l) ->
        let l' = List.fold_left Dependencies.union Dependencies.empty
          (List.map (depend_expression program cls meth) l)
        and cls' = Program.find_class program c in
        let dep = { Dependency.name = cls'.Class.name;
                    version = Class.version cls' }
        in
          Dependencies.union l' (Dependencies.singleton dep)
    | Choose (_, v, _, p) -> assert false
    | Forall (_, v, _, p) -> assert false
    | Exists (_, v, _, p) -> assert false
    | ObjLit _ -> Dependencies.empty
    | LabelLit _ -> Dependencies.empty
    | Expression.Extern _ -> Dependencies.empty
    | SSAId _ | Phi _ -> Dependencies.empty

let depend_lhs program cls meth =
  function
    | LhsId (_, n) ->
        begin
          try
            let _ = Method.find_variable meth n in Dependencies.empty
          with Not_found ->
            let cls' = Program.find_class_of_attr program cls n in
              Dependencies.singleton { Dependency.name = cls'.Class.name;
                                       version = Class.version cls' }
        end
    | LhsAttr (_, n, (Type.Basic c)) ->
        let c' = Program.find_class program c in
        let cls' = Program.find_class_of_attr program c' n in
          Dependencies.singleton { Dependency.name = cls'.Class.name;
                                   version = Class.version cls' }
    | LhsWildcard _ -> Dependencies.empty
    | LhsSSAId _ -> Dependencies.empty


let rec depend_statement program cls meth =
  function
    | Skip n -> Dependencies.empty
    | Assert (_, e) -> depend_expression program cls meth e
    | Prove (_, e) -> depend_expression program cls meth e
    | Assign (n, lhs, rhs) ->
      let lhs' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) lhs)
      and rhs' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) rhs)
      in
        Dependencies.union lhs' rhs'
    | Await (_, c) -> depend_expression program cls meth c
    | Posit (_, c) -> depend_expression program cls meth c
    | Release n -> Dependencies.empty
    | AsyncCall (_, l, c, _, _, a) ->
      let l' =
        match l with
          | None -> Dependencies.empty
          | Some l'' -> depend_lhs program cls meth l''
      and c' = depend_expression program cls meth c
      and a' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) a)
      in
        Dependencies.union l' (Dependencies.union c' a')
    | Get (n, l, p) ->
      let l' = depend_expression program cls meth l
      and p' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) p)
      in
        Dependencies.union l' p'
    | Free (_, l) -> 
       List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) l)
    | Bury (_, l) ->
       List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) l)
    | SyncCall (_, c, _, _, i, o) ->
      let c' = depend_expression program cls meth c
      and i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      and o' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) o)
      in
        Dependencies.union c' (Dependencies.union i' o')
    | AwaitSyncCall (_, c, _, _, i, o) ->
      let c' = depend_expression program cls meth c
      and i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      and o' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) o)
      in
        Dependencies.union c' (Dependencies.union i' o')
    | LocalAsyncCall (n, l, m, s, ub, lb, i) ->
      let l' =
        match l with
          | None -> Dependencies.empty
          | Some l'' -> depend_lhs program cls meth l''
      and i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      and m' =
        let c' =
          try
            Program.find_class_of_method program cls m s
          with
            | Not_found ->
                Messages.error n.Statement.file n.Statement.line
		  ("Method " ^ m ^ " not found in class " ^ cls.Class.name) ;
		exit 1
        in
	  Dependencies.singleton { Dependency.name = c'.Class.name;
                                   version = Class.version c' }
      in
        Dependencies.union m' (Dependencies.union l' i')
    | LocalSyncCall (n, m, s, _, _, i, o)
    | AwaitLocalSyncCall (n, m, s, _, _, i, o) ->
      let i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      and m' =
        let c' =
          try
            Program.find_class_of_method program cls m s
          with
            | Not_found ->
                Messages.error n.Statement.file n.Statement.line
		  ("Method " ^ m ^ " not found in class " ^ cls.Class.name) ;
		exit 1
        in
	  Dependencies.singleton { Dependency.name = c'.Class.name;
                                   version = Class.version c' }
      and o' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_lhs program cls meth) o)
      in
        Dependencies.union m' (Dependencies.union i' o')
    | MultiCast (_, c, _, _, i) ->
      let c' = depend_expression program cls meth c
      and i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      in
        Dependencies.union c' i'
    | Tailcall (_, c, _, _, i) ->
      let c' = depend_expression program cls meth c
      and i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      in
        Dependencies.union c' i'
    | StaticTail (n, m, s, u, l, i) ->
      let i' = List.fold_left Dependencies.union Dependencies.empty
        (List.map (depend_expression program cls meth) i)
      and m' =
        let c' =
          try
            Program.find_class_of_method program cls m s
          with
            | Not_found ->
                Messages.error n.Statement.file n.Statement.line
		  ("Method " ^ m ^ " not found in class " ^ cls.Class.name) ;
		exit 1
        in
	  Dependencies.singleton { Dependency.name = c'.Class.name;
                                   version = Class.version c' }
      in
        Dependencies.union m' i'
    | If (_, c, l, r) ->
        let c' = (depend_expression program cls meth c)
        and l' = (depend_statement program cls meth l)
        and r' = (depend_statement program cls meth r)
        in
          Dependencies.union c' (Dependencies.union l' r')
    | While (_, c, i, b) ->
        let c' = (depend_expression program cls meth c)
        and i' = (depend_expression program cls meth i)
        and b' = (depend_statement program cls meth b)
        in
	  Dependencies.union c' (Dependencies.union i' b')
    | DoWhile (_, c, i, b) ->
        let c' = (depend_expression program cls meth c)
        and i' = (depend_expression program cls meth i)
        and b' = (depend_statement program cls meth b)
        in
	  Dependencies.union c' (Dependencies.union i' b')
    | Sequence (_, s1, s2) ->
        let s1' = depend_statement program cls meth s1
        and s2' = depend_statement program cls meth s2
        in
	  Dependencies.union s1' s2'
    | Merge (_, s1, s2) ->
        let s1' = depend_statement program cls meth s1
        and s2' = depend_statement program cls meth s2
        in
	  Dependencies.union s1' s2'
    | Choice (_, s1, s2) ->
        let s1' = depend_statement program cls meth s1
        and s2' = depend_statement program cls meth s2
        in
	  Dependencies.union s1' s2'
    | Return (_, r) ->
        List.fold_left Dependencies.union Dependencies.empty
          (List.map (depend_expression program cls meth) r)
    | Continue (_, c) -> depend_expression program cls meth c
    | Extern (n, s) -> Dependencies.empty


let depend_method program cls meth =
  match meth.Method.body with
      None -> Dependencies.empty
    | Some b -> depend_statement program cls meth b


let depend_with program cls w =
   List.fold_left Dependencies.union Dependencies.empty
    (List.map (depend_method program cls) w.With.methods)

let depend_class program cls =
    List.fold_left Dependencies.union Dependencies.empty
      (List.map (depend_with program cls) cls.Class.with_defs)


let depend_new_class program update =
    try
      ignore (Program.find_class program update.NewClass.cls.Class.name) ;
      raise (Failure "Class exists")
    with
      | Not_found ->
          let program' = Program.add_class program update.NewClass.cls in
          let deps = depend_class program' update.NewClass.cls in
          let p d = d.Dependency.name <> update.NewClass.cls.Class.name in
            Dependencies.filter p deps



let depend_update program update =
  let cls =
    try
      Program.find_class program update.Update.name
    with
      | Not_found ->
          let file = update.Update.file
          and line = update.Update.line
          and msg = "Class " ^ update.Update.name ^ " not found"
          in
            Messages.error file line msg; exit 1
  in
  let program' =
    Program.apply_updates program (Program.make [Declaration.Update update])
  in
  let cls' = Program.find_class program' cls.Class.name in
  let deps = List.fold_left Dependencies.union Dependencies.empty
    (List.map (depend_with program' cls') update.Update.with_defs)
  in
    Dependencies.add { Dependency.name = cls.Class.name;
                       version = Class.version cls } deps



let depend_retract program update =
  let subclasses = Program.subclasses program update.Retract.name
  and f c a =
    let cls = Program.find_class program c in
      Dependencies.add { Dependency.name = cls.Class.name; version = Class.version cls } a
  in
    IdSet.fold f subclasses Dependencies.empty



let depend_declaration program =
  function
    | Declaration.Class _ | Declaration.Interface _ | Declaration.Datatype _
    | Declaration.Exception _ | Declaration.Function _
    | Declaration.Object _ as decl ->
        decl
    | Declaration.NewClass update ->
        let deps = depend_new_class program update in
          Declaration.NewClass { update with NewClass.dependencies = deps }
    | Declaration.Update update ->
        let deps = depend_update program update in
          Declaration.Update { update with Update.dependencies = deps }
    | Declaration.Retract update ->
        let deps = depend_retract program update in
          Declaration.Retract { update with Retract.dependencies = deps }



let depend program updates =
  let upd = updates.Program.decls in
    Program.make (List.map (depend_declaration program) upd)
  
