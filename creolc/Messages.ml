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

(*s Write messages to the error stream.  These are all logging
  messages, warnings and error messages.  Also provides functions for
  enabling and disabling the printing of such messages.
*)

(*s A very simple logging facility.  

  The variable [verbose] controls how much logging the compiler will
  actually print. *)

let verbose = ref 0

(* The function [message] prints a logging message. *)

let message lvl msg = if !verbose >= lvl then prerr_endline msg


(*s Write an error message.

  This function is used to print error messages using a common
  format. *)

let error file line message =
  prerr_endline (file ^ ":" ^ (string_of_int line) ^ ": " ^ message)


(*s Print a warning message if applicable. *)

(* The different kinds of warning we want to have *)
type warning =
    Unused
    | Undefined
    | MissingInit
    | MissingRun

let warnings =
  [("unused", Unused, "Warn if a variable is declared but not unused");
   ("undefined", Undefined, "Warn if a variable is used before it is defined");
   ("init", MissingInit, "Warn if the init method is not defined");
   ("run", MissingRun, "Warn if the run method is not defined");
  ]

let help_warnings () =
  let line current (name, _, help) =
    current ^ "    " ^ name ^
      (String.make (11 - String.length name) ' ') ^
      help ^ "\n"
  in
    (List.fold_left line "" warnings) ^
      "    all        all passes mentioned above."


(* Map a warning to its name *)
let string_of_warning w =
  let (r, _, _) = List.find (fun (_, i, _) -> w = i) warnings in r

(* Map a string representing a warning name to a warning.  May raise a
   pattern matching exception. *)
let warning_of_string s =
  let (_, r, _) =
    try
      List.find (fun (n, _, _) -> n = s) warnings
    with
	Not_found -> raise (Arg.Bad ("Warning " ^ s ^ " not defined"))
  in
    r


(* A list of enabled warnings. *)
let enabled = ref []


(* Enable a list of warnings *)

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

(* Disbale a warning *)

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

(* Print a warning *)

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
