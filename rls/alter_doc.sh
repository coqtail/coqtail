#!/bin/sh

# (C) Copyright 2010, COQTAIL team
# 
# Project Info: http://sourceforge.net/projects/coqtail/
# 
# This library is free software; you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation; either version 2.1 of the License, or
# (at your option) any later version.
# 
# This library is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
# License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
# USA.

# subscript of the Makefile to generate a correct documentation

mkdir -p doc
cp coqdoc.css index.css doc/
cd doc
if [ -f index.html ]
then
	rm index.html
	
	echo '<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"\n"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">\n<html xmlns="http://www.w3.org/1999/xhtml">\n<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>\n<link href="coqdoc.css" rel="stylesheet" type="text/css"/>\n<link href="index.css" rel="stylesheet" type="text/css"/>\n<title>Documentation | Coqtail ' > list

	echo '</title>\n</head>\n<body>\n<h1>Documentation (r' >> list
	echo $rev >> list
	echo ')</h1><div id="main">' >> list
	for i in `ls *.html | sed 's/\..*//' | uniq`
	do
		echo "<h2 class=\"doc\">$i</h2>" >> list
		echo "<ul>" >> list
		ls $i*.html | sed 's/^\(.*\)\.\(.*\).html$/<li><a href="\1.\2.html">\2<\/a><\/li>/' >> list
		echo "</ul>" >> list
	done
	echo '\n</div>\n</body>\n</html>' >> list
	mv list index.html

else
	echo "index.html not found. Script should be called by make"
fi
cd ..

