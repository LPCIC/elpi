(* Copyright (C) 2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id: pa_unicode_macro.ml 8052 2008-01-10 22:32:03Z tassi $ *)

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

let loc = Stdpp.make_loc (-1, -1)

let expand_unicode_macro macro =
  debug_print (lazy (Printf.sprintf "Expanding macro '%s' ..." macro));
  let expansion = Utf8Macro.expand macro in
  <:expr< $str:expansion$ >>

let _ =
  Quotation.add "unicode"
    (Quotation.ExAst (expand_unicode_macro, (fun _ -> assert false)))

open Pa_extend

EXTEND
  symbol: FIRST
    [
      [ x = UIDENT; q = QUOTATION ->
        let (quotation, arg) =
          let pos = String.index q ':' in
          (String.sub q 0 pos,
           String.sub q (pos + 1) (String.length q - pos - 1))
        in
        debug_print (lazy (Printf.sprintf "QUOTATION = %s; ARG = %s" quotation arg));
        if quotation = "unicode" then 
          AStok (loc, x, Some (ATexpr (loc, expand_unicode_macro arg)))
        else
          assert false
      ]
    ];
END

