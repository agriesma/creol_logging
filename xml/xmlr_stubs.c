/*
 * xmlr_stubs.c -- OCaml bindings for libxml's XmlTextWriter.
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
 */

#include "xml_helpers.h"

#include <libxml/xmlreader.h>





#define XmlReader_val(v) (*(xmlTextReaderPtr*)Data_custom_val(v))


#ifndef NDEBUG
static int debug = 0;

CAMLprim value
xmlr_set_debug(value val)
{
	CAMLparam1 (val);
	int _debug = Bool_val(val);

	if (debug || _debug) {
		fprintf(stderr, "XmlReader: setting debug to %d\n", _debug);
		fflush(stderr);
	}
	debug = _debug;
	CAMLreturn (Val_unit);
}

#else

CAMLprim value
xmlr_set_debug(value val)
{
	CAMLparam1 (val);
	CAMLreturn (Val_unit);
}

#endif





static void xml_reader_finalize(value v)
{
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XmlReader: finalize %p\n", XmlReader_val(v));
		fflush(stderr);
	}
#endif
	xmlTextReaderClose(XmlReader_val(v));
	/* XXX: api docs say this can fail. */
}





static struct custom_operations xmlr_custom_operations = {
	.identifier  = "de.berlios.oclvp.xmlreader.1",
	.finalize    = xml_reader_finalize,
	.compare     = custom_compare_default,
	.hash        = custom_hash_default,
	.serialize   = custom_serialize_default,
	.deserialize = custom_deserialize_default,
};





static int
load_opts(value vopts)
{
	CAMLparam1(vopts);
	CAMLlocal1(vlist);
	int opts = 0;
	
	if (!Is_long(vopts)) /* None */
		for (vlist = Field(vopts, 0); Is_block(vlist); vlist = Field(vlist, 1))
			opts |= 1 << Int_val(Field(vlist, 0));

	CAMLreturn(Val_int(opts));
}





static value
xml_reader_new(xmlTextReaderPtr reader)
{
	CAMLparam0();
	CAMLlocal1(vreader);
	vreader = caml_alloc_custom(&xmlr_custom_operations, 4, 0, 1);
	Field(vreader, 1) = (value)reader;
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XmlReader: wrapped %p\n",
			XmlReader_val(vreader));
		fflush(stderr);
	}
#endif
	CAMLreturn(vreader);
}





CAMLprim value
xml_reader_from_filename(value vencoding, value vopts, value filename)
{
	CAMLparam3(vencoding, vopts, filename);
	xmlTextReaderPtr reader;
	
	reader = xmlReaderForFile(String_val(filename),
				  String_val(xml_string_option(vencoding)),
				  load_opts(vopts));

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XmlReader: create reader %p from file %s\n",
			reader, String_val(filename));
		fflush(stderr);
	}
#endif

	CAMLreturn(xml_reader_new(reader));
}





CAMLprim value
xml_reader_from_string(value baseurl, value encoding, value opts, value str)
{
	CAMLparam4(baseurl, encoding, opts, str);
	xmlTextReaderPtr reader;
	
	/* XXX we probably need to hold a reference to the string? */
	reader = xmlReaderForMemory(String_val(str),
				    caml_string_length(str),
				    String_val(xml_string_option(baseurl)),
				    String_val(xml_string_option(encoding)),
				    load_opts(opts));

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XmlReader: create reader %p from string %s\n",
			reader, String_val(str));
		fflush(stderr);
	}
#endif
	CAMLreturn(xml_reader_new(reader));
}





CAMLprim value
xml_reader_read(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderRead(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderRead");
	CAMLreturn(Val_int(ret));
}





/*** current node ***/

CAMLprim value
xml_reader_get_parser_line_number(value reader)
{
	CAMLparam1(reader);
	int ret;

	ret = xmlTextReaderGetParserLineNumber(XmlReader_val(reader));
	CAMLreturn(Int_val(ret));
}





CAMLprim value
xml_reader_nodetype(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderNodeType(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderNodeType");
	CAMLreturn(Val_int(ret));
}





CAMLprim value
xml_reader_name(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;

	ret = xmlTextReaderConstName(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderConstName");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_has_value(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderHasValue(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderHasValue");
	CAMLreturn(Val_int(ret));
}





CAMLprim value
xml_reader_value(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;
	
	ret = xmlTextReaderConstValue(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderConstValue");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_base_uri(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;
	
	ret = xmlTextReaderBaseUri(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderBaseUri");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_local_name(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;
	
	ret = xmlTextReaderConstLocalName(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderConstLocalName");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_namespace_uri(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;
	
	ret = xmlTextReaderConstNamespaceUri(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderConstNamespaceUri");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_prefix(value reader)
{
	CAMLparam1(reader);
	const xmlChar *ret;
	
	ret = xmlTextReaderConstPrefix(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderConstPrefix");
	CAMLreturn(caml_copy_string((char*) ret));
}





CAMLprim value
xml_reader_is_empty_element(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderIsEmptyElement(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderIsEmptyElement");
	CAMLreturn(Val_int(ret));
}





CAMLprim value
xml_reader_depth(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderDepth(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderDepth");
	CAMLreturn(Val_int(ret));
}




#if 0
/* XXX doesn't work--unimplemented in libxml itself */
CAMLprim value
xml_reader_inner_xml(value reader) {
	CAMLparam1(reader);
	CAMLlocal1(cret);
	xmlChar* ret;
	
	ret = xmlTextReaderReadInnerXml(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderReadInnerXml");
	cret = caml_copy_string(ret);
	xmlFree(ret);
	CAMLreturn(cret);
}





CAMLprim value
xml_reader_outer_xml(value reader) {
	CAMLparam1(reader);
	CAMLlocal1(cret);
	xmlChar* ret;
	
	ret = xmlTextReaderReadOuterXml(XmlReader_val(reader));
	if (ret == NULL)
		caml_failwith("xmlTextReaderReadOuterXml");
	cret = caml_copy_string(ret);
	xmlFree(ret);
	CAMLreturn(cret);
}
#endif





CAMLprim value
xml_reader_has_attributes(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderHasAttributes(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderHasAttributes");
	CAMLreturn(Val_int(ret));
}





CAMLprim value
xml_reader_attribute_count(value reader)
{
	CAMLparam1(reader);
	int ret;
	
	ret = xmlTextReaderAttributeCount(XmlReader_val(reader));
	if (ret < 0)
		caml_failwith("xmlTextReaderAttributeCount");
	CAMLreturn(Val_int(ret));
}





CAMLprim value
xml_reader_get_attribute(value reader, value name)
{
	CAMLparam2(reader, name);
	CAMLlocal1(cret);
	xmlChar *ret;
	
	ret = xmlTextReaderGetAttribute(XmlReader_val(reader),
					BAD_CAST String_val(name));
	if (ret == NULL)
		caml_raise_not_found();
	cret = caml_copy_string((char*) ret);
	xmlFree(ret);
	CAMLreturn(cret);
}





CAMLprim value
xml_reader_get_attribute_no(value reader, value no)
{
	CAMLparam2(reader, no);
	CAMLlocal1(cret);
	xmlChar *ret;
	
	ret = xmlTextReaderGetAttributeNo(XmlReader_val(reader), Int_val(no));
	if (ret == NULL)
		caml_raise_not_found();
	cret = caml_copy_string((char*) ret);
	xmlFree(ret);
	CAMLreturn(cret);
}





CAMLprim value
xml_reader_get_attribute_ns(value reader, value name, value ns)
{
	CAMLparam3(reader, name, ns);
	CAMLlocal1(cret);
	xmlChar *ret;
	
	ret = xmlTextReaderGetAttributeNs(XmlReader_val(reader),
					  BAD_CAST String_val(name),
					  BAD_CAST String_val(ns));
	if (ret == NULL)
		caml_raise_not_found();
	cret = caml_copy_string((char*) ret);
	xmlFree(ret);
	CAMLreturn(cret);
}
