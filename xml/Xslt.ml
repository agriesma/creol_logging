(*
 * Xslt.ml -- OCaml bindings for libxslt.
 *
 * This file is part of oclvp
 *
 * Written and Copyright (c) 2005 by Marcel Kyas <mkyas@users.berlios.de>
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

type stylesheet

external set_debug: bool -> unit = "xslt_set_debug"

external parse_stylesheet_doc: Xml.doc -> stylesheet =
    "xslt_parse_stylesheet_doc"

let parse_stylesheet name = parse_stylesheet_doc (Xml.from_file name)

external transform: stylesheet -> Xml.doc -> Xml.doc = "xslt_transform"
(** Transform an XML document.

    @param stylesheet  The stylesheet used for transforming the document.
    @param source      The document to transform. *)
