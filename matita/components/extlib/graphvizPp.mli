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

(* $Id: graphvizPp.mli 6743 2006-09-04 15:51:36Z tassi $ *)

(** {2 Pretty printer for generating (textual) Graphviz markup} *)

type attribute = string * string  (* <key, value> pair *)

module type GraphvizFormatter =
  sig
    (** @param name graph name
     * @param graph_type type of dot graph, default value "digraph"
     *        interesting options: "strict digraph"
     * @param graph_attrs graph attributes
     * @param node_attrs graph-wide node attributes
     * @param edge_attrs graph-wide edge attributes *)
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

module Dot: GraphvizFormatter

