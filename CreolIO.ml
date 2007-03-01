(*
 * CreolIO.ml -- Input and Output routines for Creol.
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

(** Read and write Creol Programs.


    @author Marcel Kyas
    @version 0.0.0
    @since   0.0.0

  *)


(** Read the contents of a file and return an abstract syntax tree. *)
let from_file name =
  let lexbuf = Lexing.from_channel (open_in name) in
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- { pos with Lexing.pos_fname = name } ;
      CreolParser.main CreolLex.token lexbuf

