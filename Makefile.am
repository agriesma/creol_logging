## Makefile.am - Use automake to create Makefile.in
#
# This file is part of creoltools
#
# Written and Copyright (c) 2007 by Marcel Kyas
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
DISTCHECK_CONFIGURE_FLAGS = --disable-make-install

# Subdirs
DIST_SUBDIRS		= share info creolc tests
SUBDIRS			= share info creolc tests

MOSTLYCLEANFILES	= *~
MAINTAINERCLEANFILES	= .depend Makefile.in configure aclocal.m4 \
			  depcomp elisp-comp missing install-sh

bin_SCRIPTS		= creolshell creolbug
dist_noinst_SCRIPTS	= maude-sh
