(*
 * Config.ml -- Obtain relevant configuration information.
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

let get_library_path () =
  let home = Misc.home ()
  and library_path =
    try
      (Str.split (Str.regexp ":") (Sys.getenv "CREOL_LIBRARY_PATH"))
    with
        Not_found -> []
  in
    library_path @
      [ Version.datadir ;
        home ^ "/../share/" ^ Version.package ;
        home ^ "/../share" ;
        home ^ "/../../share/" ^ Version.package ;
        home ^ "/../../share" ;
        home ]

