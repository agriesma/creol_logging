#! /bin/sh
#
# This file is part of creoltools
#
# Written and Copyright (c) 2008 by Marcel Kyas
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

if [ -z "$1" -o -z "$2" -o -z "$3" ]
then
	echo "Usage: $0 [maude-file] [spec-file] [out-file]"
	exit 1
fi

if [ -f "$3" ]
then
	rm "$3"
fi

tmpfile1=`mktemp benchmark.XXXXXXXXXX`
tmpfile2=`mktemp benchmark.XXXXXXXXXX`

cat >> $tmpfile1 <<EOF
set trace off .
set break off .
set profile off .
EOF

cat >> $tmpfile2 <<EOF
quit .
EOF

cat "$1" "$tmpfile1" "$2" "$tmpfile2" > "$3"

rm -f "$tmpfile1" "$tmpfile2"
