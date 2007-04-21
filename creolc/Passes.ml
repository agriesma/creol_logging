(*
 * Passes.ml -- Organize the passes of the compiler.
 *
 * This file is part of creoltools
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

type pass = {
  name: string;
  help: string;
  pass: ('a, 'b) Declaration.t list -> ('c, 'd) Declaration.t list
  mutable elapsed: float;
  mutable needed: bool;
  mutable dump: bool
}

let passes = [
  { name = "";
    help = "";
    pass = check_types;
    elapsed = 0.0; needed = false; dump = false };
  { name = "";
    help = "";
    pass = simplify;
    elapsed = 0.0; needed = false; dump = false };
  { name = "";
    help = "";
    pass = lifeness;
    elapsed = 0.0; needed = false; dump = false };
  { name = "";
    help = "";
    pass = tailcalls;
    elapsed = 0.0; needed = false; dump = false };
  { name = "";
    help = "";
    pass = tailcalls;
    elapsed = 0.0; needed = false; dump = false };
]
