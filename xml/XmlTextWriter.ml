(*
 * Xmlw.ml -- OCaml bindings for libxml's xmlwriter.
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

(** *)

type xmlwriter
(** The type of the XML Text writer. *)

external set_debug: bool -> unit = "xml_writer_set_debug"
(** Whether to enable debugging output from the library.  Default is false. *)

external to_file: string -> int -> xmlwriter = "xml_writer_to_file"
(** Create an XML writer which writes to a file.

    @param uri  The file name to write to.  "-" is standard output.
    @param compression  Whether to compress.  May be a value from 0 to 9.

    @return A new text writer. *)

external end_attribute: xmlwriter -> unit = "xml_writer_end_attribute"
(** End an attribute. *)

external end_cdata: xmlwriter -> unit = "xml_writer_end_cdata"
(** End a CDATA block. *)

external end_comment: xmlwriter -> unit = "xml_writer_end_comment"
(** End a comment *)

external end_dtd: xmlwriter -> unit = "xml_writer_end_dtd"
(** End an embedded DTD *)

external end_dtd_attlist: xmlwriter -> unit = "xml_writer_end_dtd_attlist"
(** End an attribute list within the DTD *)

external end_dtd_element: xmlwriter -> unit = "xml_writer_end_dtd_element"
(** End an DTD element *)

external end_dtd_entity: xmlwriter -> unit = "xml_writer_end_dtd_entity"
(** End an DTD entity *)

external end_document: xmlwriter -> unit = "xml_writer_end_document"
(** End the document *)

external end_element: xmlwriter -> unit = "xml_writer_end_element"
(** End an element *)

external end_processing_instruction: xmlwriter -> unit = "xml_writer_end_pi"
(** End a processing instruction *)

external flush: xmlwriter -> unit = "xml_writer_flush"
(** Flush the buffer associated to the xml writer *)

external set_indent: xmlwriter -> bool -> unit = "xml_writer_set_indent"
(** Set whether the writer shall indentate the output *)

external start_attribute: xmlwriter -> string -> unit =
    "xml_writer_start_attribute"
(** Start an attribute *)

external start_attribute_namespace: xmlwriter -> string option ->
  string -> string option -> unit = "xml_writer_start_attribute_namespace"
(** Start an attribute with namespace support *)

external start_cdata: xmlwriter -> unit = "xml_writer_start_cdata"
(** Start an XML CDATA section *)

external start_comment: xmlwriter -> unit = "xml_writer_start_comment"
(** Start an XML comment *)

external start_dtd: xmlwriter -> string -> string option -> string option ->
  unit = "xml_writer_start_dtd"
(** Start an XML DTD.

    @param writer  The XML writer.
    @param name    The name of the DTD.
    @param pubid   The public identifier, which is an alternatie to the system
		   identifier.
    @param sysid   The system identifer, which is the URI of the DTD *)

external start_dtd_attlist: xmlwriter -> string ->
  unit = "xml_writer_start_dtd_attlist"
(** Start an XML DTD attribute list.

    @param writer  The XML writer.
    @param name    The name of the DTD attlist. *)

external start_dtd_element: xmlwriter -> string ->
  unit = "xml_writer_start_dtd_element"
(** Start an XML DTD element.

    @param writer  The XML writer.
    @param name    The name of the DTD element. *)

external start_dtd_entity: xmlwriter -> bool -> string ->
  unit = "xml_writer_start_dtd_entity"
(** Start an XML DTD entity.

    @param writer  The XML writer.
    @param pe      True if this is a parameter entity, false if not.
    @param name    The name of the DTD element. *)

external start_document: xmlwriter -> string option -> string option ->
  string option -> unit = "xml_writer_start_document"
(** Start an XML document.

    @param writer      The XML writer.
    @param version     The XML version ("1.0")
    @param encoding    The encoding ("UTF-8")
    @param standalone  "yes" or "no" or NULL for default. *)

external start_element: xmlwriter -> string -> unit =
    "xml_writer_start_element"
(** Start an XML element.

    @param writer  The XML writer.
    @param name    The name of the element. *)

external start_element_namespace: xmlwriter -> string option -> string ->
  string option -> unit = "xml_writer_start_element_namespace"
(** Start an XML element.

    @param writer  The XML writer.
    @param prefix  Namespace prefix of NULL.
    @param name    The name of the element.
    @param nsuri   Namespace URI or NULL. *)


external start_processing_instruction: xmlwriter -> string -> unit =
    "xml_writer_start_processing_instruction"
(** Start an XML processing instruction.

    @param writer  The XML writer.
    @param target  The target. *)

external start_attribute: xmlwriter -> string -> string -> unit =
    "xml_writer_start_attribute"
(** Start an XML attribute.

    @param writer  The XML writer.
    @param name    The attribute name.
    @param content The attribute content. *)

external start_attribute_namespace: xmlwriter -> string -> string ->
  string -> string -> unit = "xml_writer_start_attribute_namespace"

external start_cdata: xmlwriter -> unit = "xml_writer_start_cdata"

external start_comment: xmlwriter -> unit = "xml_writer_start_comment"

external start_dtd: xmlwriter -> string -> string -> string -> unit =
    "xml_writer_start_dtd"

external start_dtd_attlist: xmlwriter -> string -> string =
    "xml_writer_start_dtd_attlist"

external start_dtd_element: xmlwriter -> string -> unit =
    "xml_writer_start_dtd_element"

external start_dtd_entity: xmlwriter -> bool -> string -> unit =
    "xml_writer_start_dtd_entity"

external start_element: xmlwriter -> string -> unit =
    "xml_writer_start_element"

external start_element_namespace: xmlwriter -> string -> string -> string ->
  unit = "xml_writer_start_element_namespace"

external start_processing_instruction: xmlwriter -> string ->
  unit = "xml_writer_start_processing_instruction"

external write_attribute: xmlwriter -> string -> string ->
  unit = "xml_writer_write_attribute"

external write_attribute_namespace: xmlwriter -> string -> string -> string ->
  string -> unit = "xml_writer_write_attribute_namespace"

external write_base64: xmlwriter -> string -> int -> int -> unit =
    "xml_writer_write_base64"

external write_binhex: xmlwriter -> string -> int -> int -> unit =
    "xml_writer_write_binhex"

external write_cdata: xmlwriter -> string -> unit = "xml_writer_write_cdata"

external write_comment: xmlwriter -> string -> unit =
    "xml_writer_write_comment"

external write_dtd: xmlwriter -> string -> string -> string -> string ->
  unit = "xml_writer_write_dtd"

external write_dtd_attlist: xmlwriter -> string -> string ->
  unit = "xml_writer_write_dtd_attlist"

external write_dtd_content: xmlwriter -> string -> string ->
  unit = "xml_writer_write_dtd_content"

(* XXX: Add a prototype for xml_writer_write_dtd_external_entity *)

external write_dtd_external_entity_contents: xmlwriter -> string -> string ->
  string -> unit = "xml_writer_write_dtd_external_entity_contents"

external write_dtd_internal_entity: xmlwriter -> bool -> string -> string ->
  unit = "xml_writer_write_dtd_internal_entity"

external write_dtd_notation: xmlwriter -> string -> string -> string ->
  unit = "xml_writer_write_dtd_notation"

external write_element: xmlwriter -> string -> string option -> unit =
    "xml_writer_write_element"

external write_element_namespace: xmlwriter -> string -> string -> string ->
  string -> unit = "xml_writer_write_element_namespace"

external write_processing_instruction: xmlwriter -> string -> string ->
  unit = "xml_writer_write_processing_instruction"

external write_raw: xmlwriter -> string -> unit = "xml_writer_write_raw"

external write_raw_len: xmlwriter -> string -> int -> unit =
    "xml_writer_write_raw_len"

external write_string: xmlwriter -> string -> unit = "xml_writer_write_string"
