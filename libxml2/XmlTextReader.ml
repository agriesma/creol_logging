(*
 * XmlTextReader.ml -- OCaml bindings for libxml's XmlTextReader.
 *
 * This file is part of oclvp
 *
 * Copyright (c) 2005 by Marcel Kyas <mkyas@users.berlios.de>
 *
 * Derived from ocaml-xmlr - OCaml bindings for libxml's xmlreader.
 * Copyright (C) 2004  Evan Martin <martine@danga.com>
 *
 * License changed from LGPL to GPL for this modified version.
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

(** This module provides forward-only, read-only access to a character
    stream of XML data. This class enforces the rules of well-formed XML
    but does not perform data validation.

    The API is modelled after the XmlTextReader class of C# and conforms to
    the W3C Extensible Markup Language (XML) 1.0 and the Namespaces in XML
    recommendations.

    A given set of XML data is modeled as a tree of nodes. The different
    types of nodes are specified in the XmlNodeType enumeration. The current
    node refers to the node on which the reader is positioned. The reader
    is advanced using any of the "read" or "moveto" methods. It follows a
    list displaying properties exposed for the current node.

    - {b AttributeCount} The number of attributes on the node.
    - {b BaseUri} The base URI of the node.
    - {b Depth} The depth of the node in the tree.
    - {b HasAttributes} Whether the node has attributes.
    - {b HasValue} Whether the node can have a text value.
    - {b IsDefault} Whether an Attribute node was generated from the default
      value defined in the DTD or schema.
    - {b IsEmptyElement} Whether an Element node is empty.
    - {b LocalName} The local name of the node.
    - {b Name} The qualified name of the node, equal to Prefix:LocalName.
    - {b NamespaceUri} The URI defining the namespace associated with the
      node.
    - {b NodeType} The XmlNodeType of the node.
    - {b Prefix} A shorthand reference to the namespace associated with
      the node.
    - {b QuoteChar} The quotation mark character used to enclose the
      value of an attribute.
    - {b Value} The text value of the node.
    - {b XmlLang} The xml:lang scope within which the node resides.

    This class does not expand default attributes or resolve general
    entities. Any general entities encountered are returned as a single
    empty EntityReference node.

    This class checks that a Document Type Definition (DTD) is
    well-formed, but does not validate using the DTD.

    The functions defined here throw exceptions on XML parse errors.
    After an exception is thrown, the state of the reader is not
    predictable.  For example, the reported node type may be different
    than the actual node type of the current node.

    XXX: Check whether this holds for the API libxml2?

    The documentation of this file has been adapted from
    {{: http://dotgnu.org/pnetlib-doc/System/Xml/XmlTextReader.html}
     http://dotgnu.org/pnetlib-doc/System/Xml/XmlTextReader.html}. *)

(** Abstract data type of the text reader. *)
type xmlreader

(** A given set of XML data is modeled as a tree of nodes. This
    enumeration specifies the different node types. *)

type nodetype =
    NodeTypeNone
      (** This is returned by the XmlTextReader if a read method has not been
          called or if no more nodes are available to be read. *)
  | StartElement
      (** An element, more precisely the start of an element.

          Example XML: <name>

          An Element node can have the following child node types:
          Element , Text , Comment , ProcessingInstruction , CDATA ,
          and EntityReference . It can be the child of the Document ,
          DocumentFragment , EntityReference , and Element nodes. *)
  | Attribute
      (** An attribute.

          Example XML: id="123"

          An Attribute node can have the following child node types:
          Text and EntityReference . The Attribute node does not appear
          as the child node of any other node type. It is not considered
          a child node of an Element. *)
  | Text
  | CData
      (** A CDATA section.

          Example XML: <![CDATA[escaped text]]>

          CDATA sections are used to escape blocks of text that would
          otherwise be recognized as markup. A CDATA node cannot have
          any child nodes. It can appear as the child of the
          DocumentFragment, EntityReference, and Element nodes. *)
  | EntityRef
      (** A reference to an entity.

          Example XML: &amp;num;

          An EntityReference node can have the following child node types:
          Element , ProcessingInstruction , Comment , Text , CDATA , and
          EntityReference . It can appear as the child of the Attribute ,
          DocumentFragment , Element , and EntityReference nodes. *)
  | EntityDecl
  | PI
      (** A processing instruction.

          Example XML: <?pi test?>

          A ProcessingInstruction node cannot have any child nodes.
          It can appear as the child of the Document , DocumentFragment ,
          Element , and EntityReference nodes. *)
  | Comment
      (** A comment.

          Example XML: <!-- comment -->

          A Comment node cannot have any child nodes. It can appear as
          the child of the Document, DocumentFragment, Element, and
          EntityReference nodes. *)
  | Document
      (** A document object that, as the root of the document tree,
          provides access to the entire XML document.

          A Document node can have the following child node types:
          XmlDeclaration , Element (maximum of one), ProcessingInstruction,
          Comment, and DocumentType. It cannot appear as the child of any
          node types. *)
  | Doctype
     (** The document type declaration, indicated by the following tag.

         Example XML: <!DOCTYPE ...>

         A DocumentType node can have the following child node types:
         Notation and Entity . It can appear as the child of the Document
         node. *)
  | Fragment
      (** A document fragment.

          The DocumentFragment node associates a node or sub-tree with a
          document without actually being contained within the document.
          A DocumentFragment node can have the following child node types:
          Element, ProcessingInstruction, Comment, Text, CDATA, and
          EntityReference. It cannot appear as the child of any node types. *)
  | Notation
      (** A notation in the document type declaration.

          Example XML: <!NOTATION ...>

          A Notation node cannot have any child nodes. It can appear as
          the child of the DocumentType node. *)
  | Whitespace
  | SigWhitespace
  | EndElement
      (**  An end element.

           Example XML: </name>

           Returned when XmlTextReader gets to the end of an element. *)
  | EndEntity
      (** An entity declaration.

          Example XML: <!ENTITY ...>

          An Entity node can have child nodes that represent the expanded
          entity (for example, Text and EntityReference nodes). It can
          appear as the child of the DocumentType node. *)
  | XMLDecl

let string_of_nodetype = function
    NodeTypeNone -> "None"
  | StartElement -> "StartElement"
  | Attribute    -> "Attribute"
  | Text         -> "Text"
  | CData        -> "CData"
  | EntityRef    -> "EntityRef"
  | EntityDecl   -> "EntityDecl"
  | PI           -> "PI"
  | Comment      -> "Comment"
  | Document     -> "Document"
  | Doctype      -> "Doctype"
  | Fragment     -> "Fragment"
  | Notation     -> "Notation"
  | Whitespace   -> "Whitespace"
  | SigWhitespace-> "SigWhitespace"
  | EndElement   -> "EndElement"    
  | EndEntity    -> "EndEntity"    
  | XMLDecl      -> "XMLDecl"    

type parser_option = Recover | NoEnt | DTDLoad | DTDAttr | DTDValid |
                     NoError | NoWarning | Pedantic | NoBlanks | SAX1 |
                     XInclude | NoNet | NoDict | NSClean | NoCDATA

external from_filename : ?encoding:string -> ?opts:parser_option list -> string -> xmlreader = "xml_reader_from_filename"

external from_string : ?baseurl:string -> ?encoding:string -> ?opts:parser_option list -> string -> xmlreader = "xml_reader_from_string"

external read : xmlreader -> bool = "xml_reader_read"
external next : xmlreader -> bool = "xml_reader_next"

(** Provide the line number of the current parsing point.
    @param reader The reader providing the parse context.
    @return An integer representing the line number or 0 if not available. *)
external line_number : reader:xmlreader -> int =
  "xml_reader_get_parser_line_number"

external node_type : xmlreader -> nodetype = "xml_reader_nodetype"
external prefix : xmlreader -> string = "xml_reader_prefix"
external local_name : xmlreader -> string = "xml_reader_local_name"
external name : xmlreader -> string = "xml_reader_name"
external namespace_uri : xmlreader -> string = "xml_reader_namespace_uri"

external has_value : xmlreader -> bool = "xml_reader_has_value"

(** Obtain the value of the current node.

    @param reader The reader.

    @return The value. *)
external value : xmlreader -> string = "xml_reader_value"

external base_uri : xmlreader -> string = "xml_reader_base_uri"

external is_empty_element : xmlreader -> bool = "xml_reader_is_empty_element"
external depth : xmlreader -> int = "xml_reader_depth"

(* XXX doesn't work--unimplemented in libxml itself.
(** Reads the contents of the current node, including child nodes and markup.
   Returns a string containing the XML content. *)
external inner_xml : xmlreader -> string = "xml_reader_inner_xml"
external outer_xml : xmlreader -> string = "xml_reader_outer_xml"
*)

external has_attributes : xmlreader -> bool = "xml_reader_has_attributes"

external attribute_count : xmlreader -> int = "xml_reader_attribute_count"

external get_attribute : xmlreader -> string -> string = "xml_reader_get_attribute"

(** Get an attribute by name.  If the attribute is not defined, return default
    instead. *)
let get_attribute_opt reader name default =
  try get_attribute reader name with _ -> default

external get_attribute_no : xmlreader -> int -> string = "xml_reader_get_attribute_no"

external get_attribute_ns : xmlreader -> string -> string -> string = "xml_reader_get_attribute_ns"

let skip_to_close (r : xmlreader) (tag : string) : unit =
  if is_empty_element r then () else
  let rec skip_more () =
    if node_type r = EndElement &&
       name r = tag then
      ()
    else
      if not (read r) then raise Not_found
      else skip_more ()
  in skip_more ()

let fold_subnodes (r : xmlreader) (tag : string) (initial : 'a) 
    (f : string -> 'a -> 'a) : 'a =
  let rec read_more state =
    let nt = node_type r in
    (* stop here if we're done. *)
    if nt = EndElement && name r = tag then state else
    (* let this node update our state *)
    let newstate = 
      if nt != StartElement then state else begin
        let thistag = name r in
        let newstate = f thistag state in
        (* verify that the function read through to the closing tag. *)
        if node_type r != EndElement ||
           name r != thistag then
          skip_to_close r thistag;
        newstate
      end
    in
    (* and try to advance to the next *)
    if read r then
      read_more newstate
    else
      newstate
  in
  ignore (read r);
  read_more initial

let iter_subnodes (r : xmlreader) (tag : string) (f : string -> unit) : unit =
  fold_subnodes r tag () (fun tag _ -> f tag)
