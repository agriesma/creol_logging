/*
 * xslt_stubs.c -- OCaml bindings for libxslt.
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

#include <libxslt/xsltconfig.h>
#include <libxslt/xslt.h>
#include <libxslt/xsltInternals.h>
#include <libxslt/transform.h>
#include <libxslt/xsltutils.h>
#include <libxslt/extensions.h>


#define XsltStylesheet_val(v) (*(xsltStylesheetPtr*) Data_custom_val(v))


#ifndef NDEBUG
static int debug = 0;

CAMLprim value
xslt_set_debug(value val)
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
xslt_set_debug(value val)
{
	CAMLparam1 (val);
	CAMLreturn (Val_unit);
}

#endif


static void
xslt_stylesheet_finalize(value v)
{
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XSLT: xslt_stylesheet_finalize %p\n",
			XsltStylesheet_val (v));
		fflush(stderr);
	}
#endif
        xsltFreeStylesheet(XsltStylesheet_val(v));
}





static struct custom_operations xslt_stylesheet_custom_operations = {
        .identifier = "de.berlios.oclvp.xsltstylesheet.1",
        .finalize = xslt_stylesheet_finalize,
        .compare = custom_compare_default,
        .hash = custom_hash_default,
        .serialize = custom_serialize_default,
        .deserialize = custom_deserialize_default
};





static value
xslt_stylesheet_new(xsltStylesheetPtr arg)
{
        CAMLparam0();
        CAMLlocal1(res);
        res = caml_alloc_custom(&xslt_stylesheet_custom_operations, 4, 0, 1);
        Field(res, 1) = (value) arg;
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XSLT: wrap stylesheet %p\n",
			XsltStylesheet_val (res));
		fflush(stderr);
	}
#endif
        CAMLreturn(res);
}




static void
xslt_transform_ctxt_finalize(value v)
{
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XSLT: finalize transform context %p\n",
			XsltTransformCtxt_val(v));
		fflush(stderr);
	}
#endif
        xsltFreeTransformContext(XsltTransformCtxt_val(v));
}





static struct custom_operations xslt_transform_ctxt_custom_operations = {
        .identifier = "de.berlios.oclvp.xslttransformcontext.1",
        .finalize = xslt_transform_ctxt_finalize,
        .compare = custom_compare_default,
        .hash = custom_hash_default,
        .serialize = custom_serialize_default,
        .deserialize = custom_deserialize_default
};





static value
xslt_transform_ctxt_new(xsltTransformContextPtr arg)
{
        CAMLparam0();
        CAMLlocal1(res);
        res = caml_alloc_custom(&xslt_transform_ctxt_custom_operations, 4, 0,
				1);
        Field(res, 1) = (value) arg;
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XSLT: wrap transform context %p\n",
			XsltTransformCtxt_val(res));
		fflush(stderr);
	}
#endif
        CAMLreturn(res);
}



CAMLprim value
xslt_parse_stylesheet_doc(value doc)
{
	CAMLparam1(doc);
	xsltStylesheetPtr style;

	style = xsltParseStylesheetDoc(XmlDoc_val(doc));
	if (style == NULL || style->errors != 0) {
		if (style != NULL)
			xsltFreeStylesheet(style);
		caml_failwith("xsltParseStylesheetDoc");
	}
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "XSLT: parse style sheet %p from doc %p\n",
			style, XmlDoc_val(doc));
		fflush(stderr);
	}
#endif
	CAMLreturn (xslt_stylesheet_new(style));
}



CAMLprim value
xslt_transform(value stylesheet, value doc)
{
	CAMLparam2(stylesheet, doc);
	xmlDocPtr result, _doc = XmlDoc_val(doc);
	xsltStylesheetPtr _stylesheet = XsltStylesheet_val(stylesheet);

#ifndef NDEBUG
	if (debug) {
		fprintf(stderr,
			"XSLT: transform document %p with stylesheet %p ",
			_doc, _stylesheet);
		fflush(stderr);
	}
#endif
	result = xsltApplyStylesheet(_stylesheet, _doc, NULL);
	if (result == NULL) {
		caml_failwith("xsltApplyStylesheet");
	} else if (result->URL == NULL ) {
		result->URL = xmlStrdup(_doc->URL);
	}
#ifndef NDEBUG
	if (debug) {
		fprintf(stderr, "result = %p\n", result);
		fflush(stderr);
	}
#endif
	CAMLreturn(xml_doc_new(result));
}
