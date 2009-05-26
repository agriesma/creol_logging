(*
 * CreolLexer.mli -- Interface to the Creol lexer.
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

(** Interface to the lexical analyser of the Creol language.

    @author  Marcel Kyas
    @version 0.0
    @since   0.0

 *)


(** This exception is raised if the lexer encounters any token in the
    source code that is reserved for the Creol language but which is
    not handled by the Creol parser.

    The first parameter is the name of the file for which the exception
    is raised.  The second parameter is the line within the file.
    The final parameter is the reserved token. *)
exception Reserved of string * int * string


(** Get the next token from the buffer.

    @param lexbuf  The buffer from which we receive the tokens.

    @return The value of the token, as defined in {i Creol.mly}.

    @raise Reserved if the next token is reserved but not yet handled by
    the parser defined in {i Creol.mly} *)
val token : Lexing.lexbuf -> CreolTokens.token
