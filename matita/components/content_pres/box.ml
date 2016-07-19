(* Copyright (C) 2000-2005, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(*************************************************************************)
(*                                                                       *)
(*                           PROJECT HELM                                *)
(*                                                                       *)
(*                Andrea Asperti <asperti@cs.unibo.it>                   *)
(*                             13/2/2004                                 *)
(*                                                                       *)
(*************************************************************************)

(* $Id: box.ml 5881 2006-01-20 12:47:16Z asperti $ *)

type 
  'expr box =
    Text of attr * string
  | Space of attr
  | Ink of attr
  | H of attr * ('expr box) list
  | V of attr * ('expr box) list
  | HV of attr * ('expr box) list
  | HOV of attr * ('expr box) list
  | Object of attr * 'expr
  | Action of attr * ('expr box) list

and attr = (string option * string * string) list

let smallskip = Space([None,"width","0.5em"]);;
let skip = Space([None,"width","1em"]);;

let indent t = H([],[skip;t]);;

(* BoxML prefix *)
let prefix = "b";;

let tag_of_box = function
  | H _ -> "h"
  | V _ -> "v"
  | HV _ -> "hv"
  | HOV _ -> "hov"
  | _ -> assert false
 
let box2xml ~obj2xml box =
  let rec aux =
   let module X = Xml in
    function
        Text (attr,s) -> X.xml_nempty ~prefix "text" attr (X.xml_cdata s)
      | Space attr -> X.xml_empty ~prefix "space" attr
      | Ink attr -> X.xml_empty ~prefix "ink" attr
      | H (attr,l)
      | V (attr,l)
      | HV (attr,l)
      | HOV (attr,l) as box ->
          X.xml_nempty ~prefix (tag_of_box box) attr 
            [< (List.fold_right (fun x i -> [< (aux x) ; i >]) l [<>])
            >]
      | Object (attr,m) ->
          X.xml_nempty ~prefix "obj" attr [< obj2xml m >]
      | Action (attr,l) ->
          X.xml_nempty ~prefix "action" attr 
            [< (List.fold_right (fun x i -> [< (aux x) ; i >]) l [<>]) >]
  in
  aux box
;;

let rec map f = function
  | (Text _) as box -> box
  | (Space _) as box -> box
  | (Ink _) as box -> box
  | H (attr, l) -> H (attr, List.map (map f) l)
  | V (attr, l) -> V (attr, List.map (map f) l)
  | HV (attr, l) -> HV (attr, List.map (map f) l)
  | HOV (attr, l) -> HOV (attr, List.map (map f) l)
  | Action (attr, l) -> Action (attr, List.map (map f) l)
  | Object (attr, obj) -> Object (attr, f obj)
;;

(*
let document_of_box ~obj2xml pres =
 [< Xml.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
    Xml.xml_cdata "\n";
    Xml.xml_nempty ~prefix "box"
     [Some "xmlns","m","http://www.w3.org/1998/Math/MathML" ;
      Some "xmlns","b","http://helm.cs.unibo.it/2003/BoxML" ;
      Some "xmlns","helm","http://www.cs.unibo.it/helm" ;
      Some "xmlns","xlink","http://www.w3.org/1999/xlink"
     ] (print_box pres)
 >]
*)

let b_h a b = H(a,b)
let b_v a b = V(a,b)
let b_hv a b = HV(a,b)
let b_hov a b = HOV(a,b)
let b_text a b = Text(a,b)
let b_object b = Object ([],b)
let b_indent = indent
let b_space = Space [None, "width", "0.5em"]
let b_kw = b_text (RenderingAttrs.object_keyword_attributes `BoxML)
let b_toggle items = Action ([ None, "type", "toggle"], items)

let pp_attr attr =
  let pp (ns, n, v) =
    Printf.sprintf "%s%s=%s" (match ns with None -> "" | Some s -> s ^ ":") n v
  in
  String.concat " " (List.map pp attr)

let get_attr = function
  | Text (attr, _)
  | Space attr
  | Ink attr
  | H (attr, _)
  | V (attr, _)
  | HV (attr, _)
  | HOV (attr, _)
  | Object (attr, _)
  | Action (attr, _) ->
      attr

let set_attr attr = function
  | Text (_, x) -> Text (attr, x)
  | Space _ -> Space attr
  | Ink _ -> Ink attr
  | H (_, x) -> H (attr, x)
  | V (_, x) -> V (attr, x)
  | HV (_, x) -> HV (attr, x)
  | HOV (_, x) -> HOV (attr, x)
  | Object (_, x) -> Object (attr, x)
  | Action (_, x) -> Action (attr, x)

