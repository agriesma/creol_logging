(*
 * Messages.ml -- Display or do not display compiler messages.
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

(** The amount of noise the user wants to see. *)
let verbose = ref 0

(** Print a message, if the compiler is instructed to be noisy. *)
let message lvl msg = if !verbose >= lvl then prerr_endline msg


(** Write an error message. *)
let error file line message =
  prerr_endline (file ^ ":" ^ (string_of_int line) ^ ": " ^ message)


(** The different kinds of warning we want to have *)
type warning =
    Unused
    | Undefined
    | MissingInit
    | MissingRun

(** Map a warning to its name *)
let string_of_warning =
  function
      Unused -> "unused"
    | Undefined -> "undefined"
    | MissingInit -> "init"
    | MissingRun -> "run"

(** Map a string representing a warning name to a warning.  May raise
    a pattern matching exception. *)
let warning_of_string =
  function
      "usused" -> Unused
    | "undefined" -> Undefined
    | "init" -> MissingInit
    | "run" -> MissingRun
    | s -> raise (Arg.Bad ("unknown waring `" ^ s ^ "'"))


(** A list of enabled warnings. *)
let enabled = ref []


(** Enable a list of warnings *)
let enable arg =
  let enable_warning s =
    let w = warning_of_string s in
      if not (List.mem w !enabled) then
	enabled := w::(!enabled)
  in
    if arg <> "all" then
      List.iter enable_warning (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Enable all *)
      enabled := [ Unused ; Undefined ; MissingInit ; MissingRun ]

let disable arg =
  let disable_warning s =
    let w = warning_of_string s in
      if not (List.mem w !enabled) then
	enabled := List.filter (fun e -> e <> w) (!enabled)
  in
    if arg <> "all" then
      List.iter disable_warning (Str.split (Str.regexp "[, \t]+") arg)
    else
      (* Disable all *)
      enabled := []

let warn name file line message =
  if List.mem name !enabled then
    begin
      let msg = file ^ ":" ^ (string_of_int line) ^ ": Warning" ^
	(if !verbose > 0 then "(" ^ (string_of_warning name) ^ ")" else "") ^
	": " ^ message
      in
	prerr_string msg;
	prerr_newline ()
    end
