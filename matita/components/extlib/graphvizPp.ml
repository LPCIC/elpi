(* Copyright (C) 2006, HELM Team.
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

(* $Id: graphvizPp.ml 10839 2010-04-11 17:13:56Z fguidi $ *)

type attribute = string * string  (* <key, value> pair *)

module type GraphvizFormatter =
  sig
    val header:
      ?graph_type:string -> 
      ?name:string -> ?graph_attrs:(attribute list) ->
      ?node_attrs:(attribute list) -> ?edge_attrs:(attribute list) ->
      Format.formatter ->
        unit
    val node: string -> ?attrs:(attribute list) -> Format.formatter -> unit
    val edge:
      string -> string -> ?attrs:(attribute list) -> Format.formatter ->
        unit
    val raw: string -> Format.formatter -> unit
    val trailer: Format.formatter -> unit
  end

open Format

module Dot =
  struct
    let attribute fmt (k, v) = fprintf fmt "@[<hv2>%s=@,\"%s\",@]" k v
    let attributes attrs fmt = List.iter (attribute fmt) attrs
    let quote_string quote s = if quote then "\"" ^s ^ "\"" else s

    let node name ~quote ?(attrs = []) fmt =
      fprintf fmt "@[<hov2>%s@ [" (quote_string quote name);
      attributes attrs fmt;
      fprintf fmt "];@]@,"

    let edge ~quote name1 name2 ?(attrs = []) fmt =
      fprintf fmt "@[<hov2>%s ->@ %s@ [" 
         (quote_string quote name1) (quote_string quote name2);
      attributes attrs fmt;
      fprintf fmt "];@]@,"

    let header ?(graph_type = "digraph") ?(name = "g") ?(graph_attrs = []) ?node_attrs ?edge_attrs fmt =
      fprintf fmt "@[<hv2>%s %s {@," graph_type name;
      List.iter (fun (k, v) -> fprintf fmt "@[<hv2>%s=@,%s;@]@," k v)
        graph_attrs;
      (match node_attrs with
      | Some attrs -> node "node" ~quote:false ~attrs fmt
      | None -> ());
      (match edge_attrs with
      | Some attrs -> node "edge" ~quote:false ~attrs fmt
      | None -> ())

    let node = node ~quote:true
    let edge = edge ~quote:true
    let raw s fmt = pp_print_string fmt s
    let trailer fmt = fprintf fmt "@,}@]%!"
  end

