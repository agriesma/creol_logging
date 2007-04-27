(*
 * Messages.ml -- Display or do not display compiler messages.
 *
 * This file is part of creolcomp
 *
 * Written and Copyright (c) 2007 by Marcel Kyas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 *)

let verbose = ref 0

let message lvl msg = if !verbose > lvl then prerr_endline msg

let error file line message =
  prerr_endline (file ^ ":" ^ (string_of_int line) ^ ": " ^ message)

let unused = "unused"
let undefined = "undefined"

type warning = {
  name: string;
  help: string;
  mutable enabled: bool;
}

let warnings = [
  { name = unused;
    help = "Warn if a variable is defined but not used";
    enabled = true };
  { name = undefined;
    help = "Warn if a variable may be used without being defined";
    enabled = true }
]

module WarningMap = Map.Make(String)

let init () =
  let rec do_init map =
    function
	[] -> map
      | a::r -> WarningMap.add a.name a (do_init map r)
  in
    do_init WarningMap.empty warnings

let warnings = init ()
  (** This is the map of all warnings *)

let enable_warning name =
  let setting = WarningMap.find name warnings in
    setting.enabled <- true

let disable_warning name =
  let setting = WarningMap.find name warnings in
    setting.enabled <- false

let warn name file line message =
  if name = "error" then
    error file line message
  else
    let setting = WarningMap.find name warnings in
      if setting.enabled then
	begin
	  let msg = file ^ ":" ^ (string_of_int line) ^ ": Warning" ^
	    (* If we feel we can add the level
	       (if verbose then "(" ^ name ^ ")" ^ *)
	    ": " ^ message
	  in
	    prerr_string msg;
	    prerr_newline ()
	end
