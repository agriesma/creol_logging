(*
 * BackendCreol.mli -- Emit a tree as a Creol source file.
 *
 * This file is part of creoltools
 *
 * Written and Copyright (c) 2007, 2008 by Marcel Kyas
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

open Creol

val requires : 'a -> string list

val conflicts : 'a -> string list

val pretty_print_expression : out_channel -> Expression.t -> unit

val pretty_print_statement : out_channel -> Statement.t -> unit

val pretty_print_program : out_channel -> Program.t -> unit
