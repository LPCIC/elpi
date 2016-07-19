(*
 * Copyright (C) 2003-2004:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id: http_getter_const.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

open Printf;;

let version = "0.4.0"
let conffile = "http_getter.conf.xml"

let xhtml_ns = "http://www.w3.org/1999/xhtml"
let helm_ns = "http://www.cs.unibo.it/helm"

  (* TODO provide a better usage string *)
let usage_string configuration =
  sprintf
"<?xml version=\"1.0\"?>
<html xmlns=\"%s\" xmlns:helm=\"%s\">
  <head>
    <title>HTTP Getter's help message</title>
  </head>
  <body>
    <h1>HTTP Getter, version %s</h1>
    <h2>Usage information</h2>
    <p>
    Usage: <kbd>http://hostname:getterport/</kbd><em>command</em>
    </p>
    <p>
    Available commands:
    </p>
    <p>
      <b><kbd><a href=\"/help\">help</a></kbd></b><br />
      display this help message
    </p>
    <p>
      <b><kbd>getxml?uri=URI[&amp;format=(normal|gz)][&amp;patch_dtd=(yes|no)]</kbd></b><br />
    </p>
    <p>
      <b><kbd>resolve?uri=URI</kbd></b><br />
    </p>
    <p>
      <b><kbd>getdtd?uri=URI[&amp;patch_dtd=(yes|no)]</kbd></b><br />
    </p>
    <p>
      <b><kbd>getxslt?uri=URI[&amp;patch_dtd=(yes|no)]</kbd></b><br />
    </p>
    <p>
      <b><kbd><a href=\"/update\">update</a></kbd></b><br />
    </p>
    <p>
      <b><kbd><a href=\"clean_cache\">clean_cache</a></kbd></b><br />
    </p>
    <p>
      <b><kbd>ls?baseuri=regexp&amp;format=(txt|xml)</kbd></b><br />
    </p>
    <p>
      <b><kbd>getalluris?format=(<a href=\"/getalluris?format=txt\">txt</a>|<a href=\"/getalluris?format=xml\">xml</a>)</kbd></b><br />
    </p>
    <p>
      <b><kbd><a href=\"/getempty\">getempty</a></kbd></b><br />
    </p>
    <h2>Current configuration</h2>
    <pre>%s</pre>
  </body>
</html>
"
  xhtml_ns helm_ns
  version configuration

let empty_xml =
"<?xml version=\"1.0\"?>
<!DOCTYPE empty [
  <!ELEMENT empty EMPTY>
]>
<empty />
"

