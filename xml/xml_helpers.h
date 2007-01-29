/*
 * xml_helpers.c -- Helper functions for the OCaml XML bindings.
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

#ifndef INCLUDED_XML_HELPERS_H
#define INCLUDED_XML_HELPERS_H

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/custom.h>

#include <libxml/parser.h>
#include <libxml/tree.h>

value xml_string_option(value opt);

#define XmlDoc_val(v) (*(xmlDocPtr*) Data_custom_val(v))

value xml_doc_new(xmlDocPtr doc);

#define XsltTransformCtxt_val(v) \
	(*(xsltTransformContextPtr*) Data_custom_val(v))

#endif
