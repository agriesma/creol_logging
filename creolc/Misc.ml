(*
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

(** Fresh variable names. *)
type freshname = FreshName of string * freshvarname
and freshvarname = unit -> freshname

let fresh_name_gen p =
  let rec f n () = FreshName(p ^ (string_of_int n), f (n + 1))
  in f 0
