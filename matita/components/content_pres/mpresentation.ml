(* Copyright (C) 2000, HELM Team.
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

(**************************************************************************)
(*                                                                        *)
(*                           PROJECT HELM                                 *)
(*                                                                        *)
(*                Andrea Asperti <asperti@cs.unibo.it>                    *)
(*                             16/62003                                   *)
(*                                                                        *)
(**************************************************************************)

(* $Id: mpresentation.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

type 'a mpres = 
    Mi of attr * string
  | Mn of attr * string
  | Mo of attr * string
  | Mtext of attr * string
  | Mspace of attr
  | Ms of attr * string
  | Mgliph of attr * string
  | Mrow of attr * 'a mpres list
  | Mfrac of attr * 'a mpres * 'a mpres
  | Msqrt of attr * 'a mpres
  | Mroot of attr * 'a mpres * 'a mpres
  | Mstyle of attr * 'a mpres
  | Merror of attr * 'a mpres
  | Mpadded of attr * 'a mpres
  | Mphantom of attr * 'a mpres
  | Mfenced of attr * 'a mpres list
  | Menclose of attr * 'a mpres
  | Msub of attr * 'a mpres * 'a mpres
  | Msup of attr * 'a mpres * 'a mpres
  | Msubsup of attr * 'a mpres * 'a mpres *'a mpres 
  | Munder of attr * 'a mpres * 'a mpres
  | Mover of attr * 'a mpres * 'a mpres
  | Munderover of attr * 'a mpres * 'a mpres *'a mpres 
(* | Multiscripts of ???  NOT IMPLEMEMENTED *)
  | Mtable of attr * 'a row list
  | Maction of attr * 'a mpres list
  | Mobject of attr * 'a
and 'a row = Mtr of attr * 'a mtd list
and 'a mtd = Mtd of attr * 'a mpres
and attr = (string option * string * string) list
;;

let smallskip = Mspace([None,"width","0.5em"]);;
let indentation = Mspace([None,"width","1em"]);;

let indented elem =
  Mrow([],[indentation;elem]);;

let standard_tbl_attr = 
  [None,"align","baseline 1";None,"equalrows","false";None,"columnalign","left"]
;;

let two_rows_table attr a b =
  Mtable(attr@standard_tbl_attr,
    [Mtr([],[Mtd([],a)]);
     Mtr([],[Mtd([],b)])]);;

let two_rows_table_with_brackets attr a b op =
  (* only the open bracket is added; the closed bracket must be in b *)
  Mtable(attr@standard_tbl_attr,
    [Mtr([],[Mtd([],Mrow([],[Mtext([],"(");a]))]);
     Mtr([],[Mtd([],Mrow([],[indentation;op;b]))])]);;

let two_rows_table_without_brackets attr a b op =
  Mtable(attr@standard_tbl_attr,
    [Mtr([],[Mtd([],a)]);
     Mtr([],[Mtd([],Mrow([],[indentation;op;b]))])]);;

let row_with_brackets attr a b op =
  (* by analogy with two_rows_table_with_brackets we only add the
     open brackets *)
  Mrow(attr,[Mtext([],"(");a;op;b;Mtext([],")")])

let row_without_brackets attr a b op =
  Mrow(attr,[a;op;b])

(* MathML prefix *)
let prefix = "m";;
 
let print_mpres obj_printer mpres =
 let module X = Xml in
 let rec aux =
    function
      Mi (attr,s) -> X.xml_nempty ~prefix "mi" attr (X.xml_cdata s)
    | Mn (attr,s) -> X.xml_nempty ~prefix "mn" attr (X.xml_cdata s)
    | Mo (attr,s) ->
        let s =
          let len = String.length s in
          if len > 1 && s.[0] = '\\'
          then String.sub s 1 (len - 1)
          else s
        in
        X.xml_nempty ~prefix "mo" attr (X.xml_cdata s)
    | Mtext (attr,s) -> X.xml_nempty ~prefix "mtext" attr (X.xml_cdata s)
    | Mspace attr -> X.xml_empty ~prefix "mspace" attr
    | Ms (attr,s) -> X.xml_nempty ~prefix "ms" attr (X.xml_cdata s)
    | Mgliph (attr,s) -> X.xml_nempty ~prefix "mgliph" attr (X.xml_cdata s)
    (* General Layout Schemata *)
    | Mrow (attr,l) ->
        X.xml_nempty ~prefix "mrow" attr 
           [< (List.fold_right (fun x i -> [< (aux x) ; i >]) l [<>])
            >]
    | Mfrac (attr,m1,m2) ->
         X.xml_nempty ~prefix "mfrac" attr [< aux m1; aux m2 >]
    | Msqrt (attr,m) ->
         X.xml_nempty ~prefix "msqrt" attr [< aux m >]
    | Mroot  (attr,m1,m2) ->
         X.xml_nempty ~prefix "mroot" attr [< aux m1; aux m2 >]
    | Mstyle (attr,m) -> X.xml_nempty ~prefix "mstyle" attr [< aux m >]
    | Merror (attr,m) -> X.xml_nempty ~prefix "merror" attr [< aux m >]
    | Mpadded (attr,m) -> X.xml_nempty ~prefix "mpadded" attr [< aux m >]
    | Mphantom (attr,m) -> X.xml_nempty ~prefix "mphantom" attr [< aux m >]
    | Mfenced (attr,l) ->
        X.xml_nempty ~prefix "mfenced" attr 
           [< (List.fold_right (fun x i -> [< (aux x) ; i >]) l [<>])
            >]
    | Menclose (attr,m) -> X.xml_nempty ~prefix "menclose" attr [< aux m >]
    (* Script and Limit Schemata *)
    | Msub (attr,m1,m2) ->
        X.xml_nempty ~prefix "msub" attr [< aux m1; aux m2 >]
    | Msup (attr,m1,m2) ->
        X.xml_nempty ~prefix "msup" attr [< aux m1; aux m2 >]
    | Msubsup (attr,m1,m2,m3) ->
        X.xml_nempty ~prefix "msubsup" attr [< aux m1; aux m2; aux m3 >]
    | Munder (attr,m1,m2) ->
        X.xml_nempty ~prefix "munder" attr [< aux m1; aux m2 >]
    | Mover (attr,m1,m2) ->
        X.xml_nempty ~prefix "mover" attr [< aux m1; aux m2 >]
    | Munderover (attr,m1,m2,m3) ->
        X.xml_nempty ~prefix "munderover" attr [< aux m1; aux m2; aux m3 >]
  (* | Multiscripts of ???  NOT IMPLEMEMENTED *)
    (* Tables and Matrices *)
    | Mtable (attr, rl) ->
        X.xml_nempty ~prefix "mtable" attr 
           [< (List.fold_right (fun x i -> [< (aux_mrow x) ; i >]) rl [<>]) >]
    (* Enlivening Expressions *)
    | Maction (attr, l) ->
        X.xml_nempty ~prefix "maction" attr 
          [< (List.fold_right (fun x i -> [< (aux x) ; i >]) l [<>]) >]
    | Mobject (attr, obj) ->
        let box_stream = obj_printer obj in
        X.xml_nempty ~prefix "semantics" attr
          [< X.xml_nempty ~prefix "annotation-xml" [None, "encoding", "BoxML"]
              box_stream >]
          
  and aux_mrow =
   let module X = Xml in
   function 
      Mtr (attr, l) -> 
        X.xml_nempty ~prefix "mtr" attr 
           [< (List.fold_right (fun x i -> [< (aux_mtd x) ; i >]) l [<>])
            >]
  and aux_mtd =
    let module X = Xml in
    function 
       Mtd (attr,m) -> X.xml_nempty ~prefix "mtd" attr
        [< (aux m) ;
            X.xml_nempty ~prefix "mphantom" []
              (X.xml_nempty ~prefix "mtext" [] (X.xml_cdata "(")) >]
  in
  aux mpres
;;

let document_of_mpres pres =
 [< Xml.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
    Xml.xml_cdata "\n";
    Xml.xml_nempty ~prefix "math"
     [Some "xmlns","m","http://www.w3.org/1998/Math/MathML" ;
      Some "xmlns","helm","http://www.cs.unibo.it/helm" ;
      Some "xmlns","xlink","http://www.w3.org/1999/xlink"
     ] (Xml.xml_nempty ~prefix "mstyle" [None, "mathvariant", "normal"; None,
     "rowspacing", "0.6ex"] (print_mpres (fun _ -> assert false) pres))
 >]

let get_attr = function
  | Maction (attr, _)
  | Menclose (attr, _)
  | Merror (attr, _)
  | Mfenced (attr, _)
  | Mfrac (attr, _, _)
  | Mgliph (attr, _)
  | Mi (attr, _)
  | Mn (attr, _)
  | Mo (attr, _)
  | Mobject (attr, _)
  | Mover (attr, _, _)
  | Mpadded (attr, _)
  | Mphantom (attr, _)
  | Mroot (attr, _, _)
  | Mrow (attr, _)
  | Ms (attr, _)
  | Mspace attr
  | Msqrt (attr, _)
  | Mstyle (attr, _)
  | Msub (attr, _, _)
  | Msubsup (attr, _, _, _)
  | Msup (attr, _, _)
  | Mtable (attr, _)
  | Mtext (attr, _)
  | Munder (attr, _, _)
  | Munderover (attr, _, _, _) ->
      attr

let set_attr attr = function
  | Maction (_, x) -> Maction (attr, x)
  | Menclose (_, x) -> Menclose (attr, x)
  | Merror (_, x) -> Merror (attr, x)
  | Mfenced (_, x) -> Mfenced (attr, x)
  | Mfrac (_, x, y) -> Mfrac (attr, x, y)
  | Mgliph (_, x) -> Mgliph (attr, x)
  | Mi (_, x) -> Mi (attr, x)
  | Mn (_, x) -> Mn (attr, x)
  | Mo (_, x) -> Mo (attr, x)
  | Mobject (_, x) -> Mobject (attr, x)
  | Mover (_, x, y) -> Mover (attr, x, y)
  | Mpadded (_, x) -> Mpadded (attr, x)
  | Mphantom (_, x) -> Mphantom (attr, x)
  | Mroot (_, x, y) -> Mroot (attr, x, y)
  | Mrow (_, x) -> Mrow (attr, x)
  | Ms (_, x) -> Ms (attr, x)
  | Mspace _ -> Mspace attr
  | Msqrt (_, x) -> Msqrt (attr, x)
  | Mstyle (_, x) -> Mstyle (attr, x)
  | Msub (_, x, y) -> Msub (attr, x, y)
  | Msubsup (_, x, y, z) -> Msubsup (attr, x, y, z)
  | Msup (_, x, y) -> Msup (attr, x, y)
  | Mtable (_, x) -> Mtable (attr, x)
  | Mtext (_, x) -> Mtext (attr, x)
  | Munder (_, x, y) -> Munder (attr, x, y)
  | Munderover (_, x, y, z) -> Munderover (attr, x, y, z)

