(*i
 * Misc.ml -- Different auxiluary functions.
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
 * along with this program.   If not, see <http://www.gnu.org/licenses/>.
i*)

(*s


*)

let rec separated_list elt_fun sep_fun =
  (** Helper function for outputting a separated list.
      It will call [elt_fun] for each element of the list and
      [sep_fun] between each element, *)
  function
      [] -> ()
    | [s] -> elt_fun s
    | s::r ->
        elt_fun s;
        sep_fun ();
        separated_list elt_fun sep_fun r

let fold_with_sep f s a l =
  let rec work =
    function
        [] -> a
      | [e] -> f e a
      | e::r -> s (f e) (work r)
  in
    work l


(* Try to find the home directory of this binary, first by looking at
   the executable name and then by searching through the \texttt{PATH}
   environment variable.
*)
let home () =
  let exec_name = Sys.executable_name in
    if String.contains exec_name '/' then
      begin
        let lastsep = String.rindex exec_name '/' in
	  String.sub exec_name 0 lastsep
      end
    else
      begin
	(* Try to find us somewhere in the path *)
	  let path = (Str.split (Str.regexp ":") (Sys.getenv "PATH")) in
	    List.find (fun p -> Sys.file_exists (p ^ "/" ^ exec_name)) path
	end


let find_file_in_path (path: string list) (name: string) =
  let exists_p dir = Sys.file_exists (dir ^ "/" ^ name) in
    (List.find exists_p path) ^ "/" ^ name



(*s Fresh variable names. *)
type freshname = FreshName of string * freshvarname
and freshvarname = unit -> freshname

let fresh_name_gen p =
  let rec f n () = FreshName(p ^ (string_of_int n), f (n + 1))
  in f 0

let measure f =
  let now = Unix.gettimeofday () in
  let result = f () in
  let now' = Unix.gettimeofday () in
  let elapsed = (floor ((now' -. now) *. 1000000.0)) /. 1000.0 in
    (result, elapsed)
