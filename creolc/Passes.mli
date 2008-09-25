(*
 * Passes.mli -- Manages passes.
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

val time_emit : float ref

val help : unit -> string

val enable : string -> unit

val disable : string -> unit

val conflicts : string list -> unit

val requires : string list -> unit

val dump_after : string -> unit

val parse_from_channel : string -> in_channel -> Program.t

val parse_from_file : string -> Program.t

val parse_from_files : string list -> Program.t

val execute_passes : (string -> Program.t -> unit) -> string -> Program.t -> Program.t

val report_timings : unit -> unit
