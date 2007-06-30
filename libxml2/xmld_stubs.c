/*
 * xmld_stubs.c -- OCaml bindings for libxml2.
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
 */

#include "xml_helpers.h"





#ifndef NDEBUG
static int debug = 0;

CAMLprim value
xml_set_debug(value val)
{
	CAMLparam1 (val);
	int _debug = Bool_val(val);

	if (debug || _debug) {
		fprintf(stderr, "XSLT: setting debug to %d\n", _debug);
		fflush(stderr);
	}
	debug = _debug;
	CAMLreturn (Val_unit);
}

#else

CAMLprim value
xml_set_debug(value val)
{
	CAMLparam1 (val);
	CAMLreturn (Val_unit);
}

#endif





CAMLprim value
xml_set_line_numbers_default(value arg)
{
	CAMLparam1(arg);

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML set line numbers default %d\n",
			Bool_val(arg));
		fflush(stderr);
	}
#endif
	xmlLineNumbersDefault(Bool_val(arg));
	CAMLreturn(Val_unit);
}




CAMLprim value
xml_keep_blanks_default(value arg)
{
	CAMLparam1(arg);
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML keep blanks default %d\n",
			Bool_val(arg));
		fflush(stderr);
	}
#endif
	xmlKeepBlanksDefault(Bool_val(arg));
	CAMLreturn(Val_unit);
}



CAMLprim value
xml_substitute_entities_default(value arg)
{
	CAMLparam1(arg);
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML substitute entities default %d\n",
			Bool_val(arg));
		fflush(stderr);
	}
#endif
	xmlSubstituteEntitiesDefault(Bool_val(arg));
	CAMLreturn(Val_unit);
}



CAMLprim value
xml_load_ext_dtd_default(value arg)
{
	CAMLparam1(arg);
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML load external DTD default %d\n",
			Bool_val(arg));
		fflush(stderr);
	}
#endif
	xmlLoadExtDtdDefaultValue = Bool_val(arg);
	CAMLreturn(Val_unit);
}


CAMLprim value
xml_default_sax_handler_init(void)
{
	CAMLparam0();
	xmlDefaultSAXHandlerInit();
	xmlDefaultSAXHandler.cdataBlock = NULL;
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML default sax handler init.\n");
		fflush(stderr);
	}
#endif
	CAMLreturn(Val_unit);
}



/* ************************************************************************* */

/* Represent an XML document. */

static void
xml_doc_finalize(value v)
{
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML finalize document %p\n", XmlDoc_val(v));
		fflush(stderr);
	}
#endif
	xmlFreeDoc(XmlDoc_val(v));
}





static struct custom_operations xml_doc_custom_operations = {
	.identifier = "de.berlios.oclvp.xmldoc.1",
	.finalize = xml_doc_finalize,
	.compare = custom_compare_default,
	.hash = custom_hash_default,
	.serialize = custom_serialize_default,
	.deserialize = custom_deserialize_default
};





value
xml_doc_new(xmlDocPtr doc)
{
	CAMLparam0();
	CAMLlocal1(res);
	res = caml_alloc_custom(&xml_doc_custom_operations, 4, 0, 1);
	Field(res, 1) = (value) doc;
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML wrap document %p\n", XmlDoc_val(res));
		fflush(stderr);
	}
#endif
	CAMLreturn(res);
}




CAMLprim value
xml_doc_from_file(value filename)
{
	CAMLparam1(filename);
	xmlDocPtr doc;

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XML parse file %s\n", String_val(filename));
		fflush(stderr);
	}
#endif
	doc = xmlParseFile(String_val(filename));
	if (doc == NULL) {
		caml_failwith("xmlParseFile");
	}

	CAMLreturn(xml_doc_new(doc));
}





CAMLprim value
xml_doc_to_file(value doc, value name, value indent)
{
	CAMLparam3(doc, name, indent);
	int old = xmlIndentTreeOutput;

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr,
			"XML write document %p to file %s (indent = %d)\n",
			XmlDoc_val(doc), String_val(name), Bool_val(indent));
		fflush(stderr);
	}
#endif

	xmlIndentTreeOutput = Bool_val(indent);
	xmlSaveFormatFile(String_val(name), XmlDoc_val(doc), 1);
	xmlIndentTreeOutput = old;
	CAMLreturn(Val_unit);
}
