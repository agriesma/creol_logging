(*
 * Driver.ml -- The main routine.
 *
 * This file is part of creolcomp
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
    type t = Null | Creol | Dot | Maude | XML

    let target = ref Maude

    let file = ref "creolc.out"

    let options = { BackendMaude.target = BackendMaude.Interpreter;
		    red_init = false;
		    main = None }

    let set =
	function
	    "none" -> target := Null
	  | "creol" -> target := Creol
	  | "dot" -> target := Dot
	  | "maude" ->
	      options.BackendMaude.target <- BackendMaude.Interpreter ;
	      target := Maude
	  | "maudemc" ->
	      options.BackendMaude.target <- BackendMaude.Modelchecker ;
	      Passes.enable "tailcall" ;
	      target := Maude
	  | "maudert" ->
	      options.BackendMaude.target <- BackendMaude.Realtime ;
	      target := Maude
	  | "xml" -> target := XML
	  | s -> raise (Arg.Bad ("unknown target " ^ s))

    let output tree =
      let do_output out =
	Messages.message 1 "Emitting tree" ;
	match !target with
	    Null -> assert false
	  | Creol -> BackendCreol.emit out tree
	  | Dot -> BackendDot.emit out tree
	  | Maude -> BackendMaude.emit options out tree
	  | XML -> BackendXML.emit !file tree
      in
	if !target <> Null then
	  match !file with
	      "" -> assert false
            | "-" ->
		let (_, elapsed) = Misc.measure (fun () -> do_output stdout) in
		  Passes.time_emit := !Passes.time_emit +. elapsed
            | s ->
		let out = open_out s in
		let (_, elapsed) = Misc.measure (fun () -> do_output out)
		in
		  close_out out ;
		  Passes.time_emit := !Passes.time_emit +. elapsed

  end

let search_path =
  let home =
    (* Try to find the directory in which the binary has been executed. *)
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
  and library_path =
    try
      (Str.split (Str.regexp ":") (Sys.getenv "CREOL_LIBRARY_PATH"))
    with
	Not_found -> []
  in
    List.flatten [ library_path ;
                   [ Version.datadir ;
		     home ^ "/../share" ^ Version.package ;
                     home ^ "/../share" ;
                     home ] ]


let from_file name =
  (** Read the contents of a file and return an abstract syntax tree.

      @since 0.0 *)
  let exists_p d = Sys.file_exists (d ^ "/" ^ name) in
  let file =
    if ((Sys.file_exists name) || (String.contains name '/')) then
      name
    else
      try
        (List.find exists_p search_path) ^ "/" ^ name
      with
          Not_found -> prerr_endline ("cannot find " ^ name) ; exit 1
  in
  let lexbuf = Lexing.from_channel (open_in file) in
  let pos = lexbuf.Lexing.lex_curr_p in
    Messages.message 1 ("Reading " ^ file) ;
    lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = file } ;
    CreolParser.main CreolLex.token lexbuf


let from_files files =
  (** Read the contents of a list of files and return an abstract syntax
      tree.

      @since 0.0 *)
  let parse () = List.fold_left (fun a n -> (from_file n)@a) [] files in
  let (result, elapsed) = Misc.measure parse in
    Passes.time_parse := !Passes.time_parse +. elapsed; result



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
      let prelude = List.map Declaration.hide (from_file "prelude.creol") in
        Target.output (Passes.execute_passes !Target.file (prelude@tree)) ;
        if !times then Passes.report_timings () ;
        exit 0 ;;

main()
