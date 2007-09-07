(*
 * TreeLower.ml -- Transform a tree into core creol.
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

open Creol

val pass: Declaration.t list -> Declaration.t list
  (** Lower a Creol program to the "Core Creol" language.

      This function will destroy some statement and expression
      annotations.  Therefore, all semantic analysis performed before
      this function should be repeated after calling this function.

      This should only concern type inference, because all other
      analysis should be performed after this function.

      The following two invariant holds for this function:

      * A type correct program remains type correct and the
      annotations of unchanged statements are the same after
      reconstruction.

      * lower (lower tree) == lower tree *)
