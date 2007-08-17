(*
 * Driver.ml -- The main routine.
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

(** Main program.

    @author Marcel Kyas
    @version 0.0
    @since   0.0
 *)

open Creol
open Arg

let inputs : string list ref = ref []

let times = ref false

let add_input name = inputs := (!inputs)@[name]

module Target =
  struct
    type t = No | Creol | Maude | MaudeMC | XML

    let target = ref Maude

    let file = ref "creolc.out"

    let options = { BackendMaude.modelchecker = false; red_init = false;
		    main = None }

    let set =
	function
	    "none" -> target := No
	  | "creol" -> target := Creol
	  | "maude" ->
	      options.BackendMaude.modelchecker <- false ;
	      target := Maude
	  | "maudemc" ->
	      options.BackendMaude.modelchecker <- true ;
	      Passes.enable "tailcall" ;
	      target := MaudeMC
	  | "xml" -> target := XML
	  | s -> raise (Arg.Bad ("unknown target " ^ s))

    let output tree =
      let do_output out =
	Messages.message 1 "Emitting tree" ;
	match !target with
	    No -> ()
	  | Creol -> BackendCreol.emit out tree
	  | Maude | MaudeMC -> BackendMaude.emit options out tree
	  | XML -> BackendXML.emit !file tree
	in
	match !file with
          | "-" -> do_output stdout
          | s -> let out = open_out s in do_output out ; close_out out

  end

let from_file name =
  (** Read the contents of a file and return an abstract syntax tree.

      @since 0.0 *)
  let lexbuf = Lexing.from_channel (open_in name) in
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = name } ;
      CreolParser.main CreolLex.token lexbuf

let load_prelude () =
  (** Try to find the prelude and load it. *)
  let prelude_name = "prelude.creol" in
  let places = 
    try
      (Str.split (Str.regexp ":") (Sys.getenv "CREOL_LIBRARY_PATH"))
    with
	Not_found -> []
  in
  let prelude_file =
    List.find (fun d ->
      try
	let s = Unix.stat (d ^ "/" ^ prelude_name) in
	  s.Unix.st_kind = Unix.S_REG
      with
	  _ -> false) places
  in
    from_file (prelude_file ^ "/" ^ prelude_name)

let rec from_files =
  (** Read the contents of a list of files and return an abstract syntax
      tree.

      @since 0.0 *)
  function
      [] -> []
    | name::rest -> (from_file name)@(from_files rest)



let from_channel channel =
  (** Read the contents of a channel and return a abstract syntax tree.

      @since 0.0 *)
  let lexbuf = Lexing.from_channel channel in
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = "*channel*" } ;
      CreolParser.main CreolLex.token lexbuf

let show_version () =
  (** Show the name and the version of the program and exit. *)
  print_string (Version.package ^ " " ^ Version.version ^ " (" ^
		   Version.reldate ^ ")\n" );
  print_string "Copyright (c) 2007 Marcel Kyas\n";
  print_string "This is free software; see the source for copying conditions.\n";
  print_string "There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A\n";
  print_string "PARTICULAR PURPOSE.\n";
  exit 0

let main () =
  let options = [
    ("-",
     Arg.Unit (function () -> add_input "-"), "Read from standard input");
    ("-o",
     Set_string Target.file,
     "  Write the output to file");
    ("-v",
     Arg.Unit (function () -> incr Messages.verbose),
     "  Print some information while processing");
    ("-w",
     Arg.String Messages.enable,
     "[name]   Enable warning:\n" ^
     "    all        Enable all warnings");
    ("-W",
     Arg.String Messages.disable,
     " [name]   Disable the warning.  [name]s are the same as for `-w'");
    ("-p",
     Arg.String Passes.enable,
     "{name ,}  Enable passes:\n" ^ (Passes.help ()));
    ("-P",
     Arg.String Passes.disable,
     "  Disable the pass [name].  [name]s are the same as for `-t'");
    ("-d",
     Arg.String Passes.dump_after,
     "  Dump tree after [name] to out.[name].  [name]s are identical to `-p'");
    ("-times",
     Arg.Unit (function () -> times := true),
     "  Print timing information");
    ("-target",
     Arg.String Target.set,
     "[name]   Provides the target of the translation:\n" ^
     "    none       Do not generate any result\n" ^
     "    creol      Write out a creol program\n" ^
     "    maude      Write a maude file suitable for the interpreter\n" ^
     "    maudemc    Write a maude file suitable for the model checker\n" ^
     "    xml        Write the final tree as an XML file.");
    ("-main",
     Arg.String (function s -> Target.options.BackendMaude.main <- Some s),
     "  Compile the files for model checking and write the result to [file]");
    ("-red-init",
     Arg.Unit (function () ->  Target.options.BackendMaude.red_init <- true),
     "  Generate an output that will reduce init as first step.");
    ("-V", Unit show_version, "  Show the version and exit");
    ("-version", Unit show_version, "  Show the version and exit");
    ("--version", Unit show_version, "  Show the version and exit")]
  in
    parse options add_input (Sys.executable_name ^ " [options]") ;
    let tree =
      match !inputs with
	  [] ->  usage options (Sys.executable_name ^ " [options]"); exit 0
	| ["-"] -> from_channel stdin
	| _ ->  from_files !inputs
    in
      Target.output (Passes.execute_passes !Target.file
			((load_prelude ())@tree)) ;
      if !times then Passes.report_timings();
      exit 0 ;;

main()
