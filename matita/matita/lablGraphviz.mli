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

(* $Id: lablGraphviz.mli 6743 2006-09-04 15:51:36Z tassi $ *)

(** {1 LablGtk "widget" for rendering Graphviz graphs and connecting to clicks
 * on nodes, edges, ...} *)

type attribute = string * string  (* <key, value> pair *)

class type graphviz_widget =
  object

    (** Load graphviz markup from file and then:
      * 1) render it to PNG, loading the risulting image in the embedded
      *    GtkImage widget
      * 2) render it to a (HTML) map, internalizing its data.
      * Remember that map entries are generated only for nodes, (edges, ...)
      * that have an "href" (or "URL", a synonym) attribute 
      * Interesting values for gviz_cmd are:
      *   'neato'
      *   'dot'
      *   'tred | dot'
      *)
    method load_graph_from_file: ?gviz_cmd:string -> string -> unit

    (** Callback invoked when a click on a node listed in the map is received.
     * @param gdk's button event
     * @param attrs attributes of the node clicked on, as they appear on the map
     * (e.g.: [ "shape","rect"; "href","http://foo.bar.com/";
     *          "title","foo"; "alt","description"; "coords","41,6,113,54" ] *)
    method connect_href:
      (GdkEvent.Button.t -> attribute list -> unit) -> unit

    (** Center the viewport on the node having the given href value, if any *)
    method center_on_href: string -> unit

      (** {3 low level access to embedded widgets}
       * Containment hierarchy:
       *  viewport
       *    \- image *)

    method as_image: GMisc.image
    method as_viewport: GBin.viewport
  end

(** {2 Constructors} *)

val graphviz: ?packing:(GObj.widget -> unit) -> unit -> graphviz_widget

