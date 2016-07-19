(* Copyright (C) 2004-2005, HELM Team.
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

(* $Id: cicNotationPres.ml 11172 2011-01-11 21:06:37Z sacerdot $ *)

open Printf

module Ast = NotationPt
module Mpres = Mpresentation

type mathml_markup = boxml_markup Mpres.mpres
and boxml_markup = mathml_markup Box.box

type markup = mathml_markup

let atop_attributes = [None, "linethickness", "0pt"]

let to_unicode = Utf8Macro.unicode_of_tex

let rec make_attributes l1 = function
  | [] -> []
  | hd :: tl ->
      (match hd with
      | None -> make_attributes (List.tl l1) tl
      | Some s ->
          let p,n = List.hd l1 in
          (p,n,s) :: make_attributes (List.tl l1) tl)

let box_of_mpres =
  function
  | Mpresentation.Mobject (attrs, box) ->
      assert (attrs = []);
      box
  | mpres -> Box.Object ([], mpres)

let mpres_of_box =
  function
  | Box.Object (attrs, mpres) ->
      assert (attrs = []);
      mpres
  | box -> Mpresentation.Mobject ([], box)

let rec genuine_math =
  function
  | Mpresentation.Mobject ([], obj) -> not (genuine_box obj)
  | _ -> true
and genuine_box =
  function
  | Box.Object ([], mpres) -> not (genuine_math mpres)
  | _ -> true

let rec eligible_math =
  function
  | Mpresentation.Mobject ([], Box.Object ([], mpres)) -> eligible_math mpres
  | Mpresentation.Mobject ([], _) -> false
  | _ -> true

let rec promote_to_math =
  function
  | Mpresentation.Mobject ([], Box.Object ([], mpres)) -> promote_to_math mpres
  | math -> math

let small_skip =
  Mpresentation.Mspace (RenderingAttrs.small_skip_attributes `MathML)

let rec add_mpres_attributes new_attr = function
  | Mpresentation.Mobject (attr, box) ->
      Mpresentation.Mobject (attr, add_box_attributes new_attr box)
  | mpres ->
      Mpresentation.set_attr (new_attr @ Mpresentation.get_attr mpres) mpres
and add_box_attributes new_attr = function
  | Box.Object (attr, mpres) ->
      Box.Object (attr, add_mpres_attributes new_attr mpres)
  | box -> Box.set_attr (new_attr @ Box.get_attr box) box

let box_of mathonly spec attrs children =
  match children with
    | [t] -> add_mpres_attributes attrs t
    | _ ->
	let kind, spacing, indent = spec in
	let dress children =
	  if spacing then
	    NotationUtil.dress small_skip children
	  else
	    children
	in
	  if mathonly then Mpresentation.Mrow (attrs, dress children)
	  else
            let attrs' =
	      (if spacing then RenderingAttrs.spacing_attributes `BoxML else [])
              @ (if indent then RenderingAttrs.indent_attributes `BoxML else [])
              @ attrs
            in
              match kind with
                | Ast.H ->
                    if List.for_all eligible_math children then
                      Mpresentation.Mrow (attrs',
                        dress (List.map promote_to_math children))
                    else
                      mpres_of_box (Box.H (attrs',
                        List.map box_of_mpres children))
(*                 | Ast.H when List.for_all genuine_math children ->
                    Mpresentation.Mrow (attrs', dress children) *)
		| Ast.V ->
		    mpres_of_box (Box.V (attrs',
                      List.map box_of_mpres children))
		| Ast.HV ->
		    mpres_of_box (Box.HV (attrs',
                      List.map box_of_mpres children))
		| Ast.HOV ->
		    mpres_of_box (Box.HOV (attrs',
                      List.map box_of_mpres children))

let open_paren        = Mpresentation.Mo ([], "(")
let closed_paren      = Mpresentation.Mo ([], ")")
let open_bracket      = Mpresentation.Mo ([], "[")
let closed_bracket    = Mpresentation.Mo ([], "]")
let open_brace        = Mpresentation.Mo ([], "{")
let closed_brace      = Mpresentation.Mo ([], "}")
let hidden_substs     = Mpresentation.Mtext ([], "{...}")
let hidden_lctxt      = Mpresentation.Mtext ([], "[...]")
let open_box_paren    = Box.Text ([], "(")
let closed_box_paren  = Box.Text ([], ")")
let semicolon         = Mpresentation.Mo ([], ";")
let toggle_action children =
  Mpresentation.Maction ([None, "actiontype", "toggle"], children)

type child_pos = [ `Left | `Right | `Inner ]

let pp_assoc =
  function
  | Gramext.LeftA -> "LeftA"
  | Gramext.RightA -> "RightA"
  | Gramext.NonA -> "NonA"

let is_atomic t =
  let rec aux_mpres = function
    | Mpres.Mi _
    | Mpres.Mo _
    | Mpres.Mn _
    | Mpres.Ms _
    | Mpres.Mtext _
    | Mpres.Mspace _ -> true
    | Mpres.Mobject (_, box) -> aux_box box
    | Mpres.Maction (_, [mpres])
    | Mpres.Mrow (_, [mpres]) -> aux_mpres mpres
    | _ -> false
  and aux_box = function
    | Box.Space _
    | Box.Ink _
    | Box.Text _ -> true
    | Box.Object (_, mpres) -> aux_mpres mpres
    | Box.H (_, [box])
    | Box.V (_, [box])
    | Box.HV (_, [box])
    | Box.HOV (_, [box])
    | Box.Action (_, [box]) -> aux_box box
    | _ -> false
  in
  aux_mpres t

let add_parens child_prec curr_prec t =
  if is_atomic t then 
    ((*prerr_endline ("NOT adding parens around ATOMIC: "^
      BoxPp.render_to_string (function x::_->x|_->assert false)
        ~map_unicode_to_tex:false 80 t);*)t)
  else if child_prec >= 0 && child_prec < curr_prec then 
    begin 
    (*prerr_endline ("adding parens around: "^
      BoxPp.render_to_string (function x::_->x|_->assert false)
        ~map_unicode_to_tex:false 80 t);*)
    match t with
    | Mpresentation.Mobject (_, box) ->
        mpres_of_box (Box.H ([], [ open_box_paren; box; closed_box_paren ]))
    | mpres -> Mpresentation.Mrow ([], [open_paren; t; closed_paren])
  end else
    ((*prerr_endline ("NOT adding parens around: "^
      BoxPp.render_to_string (function x::_->x|_->assert false)
        ~map_unicode_to_tex:false 80 t);*)t)

let render status ~lookup_uri ?(prec=(-1)) =
  let module A = Ast in
  let module P = Mpresentation in
(*   let use_unicode = true in *)
  let make_href xmlattrs xref =
    let xref_uris =
      List.fold_right
        (fun xref uris ->
          match lookup_uri xref with
          | None -> uris
          | Some uri -> uri :: uris)
        !xref []
    in
    let xmlattrs_uris, xmlattrs =
      let xref_attrs, other_attrs =
        List.partition
          (function Some "xlink", "href", _ -> true | _ -> false)
          xmlattrs
      in
      List.map (fun (_, _, uri) -> uri) xref_attrs,
      other_attrs
    in
    let uris =
      match xmlattrs_uris @ xref_uris with
      | [] -> None
      | uris ->
          Some (String.concat " "
            (HExtlib.list_uniq (List.sort String.compare uris)))
    in
    let xrefs =
      match !xref with [] -> None | xrefs -> Some (String.concat " " xrefs)
    in
    xref := [];
    xmlattrs
    @ make_attributes [Some "helm", "xref"; Some "xlink", "href"]
        [xrefs; uris]
  in
  let make_xref xref =
    let xrefs =
      match !xref with [] -> None | xrefs -> Some (String.concat " " xrefs)
    in
    xref := [];
    make_attributes [Some "helm","xref"] [xrefs]
  in
  (* when mathonly is true no boxes should be generated, only mrows *)
  (* "xref" is  *)
  let rec aux xmlattrs mathonly xref  prec t =
    match t with
    | A.AttributedTerm _ ->
        aux_attributes xmlattrs mathonly xref  prec t
    | A.Num (literal, _) ->
        let attrs =
          (RenderingAttrs.number_attributes `MathML)
          @ make_href xmlattrs xref
        in
        Mpres.Mn (attrs, literal)
    | A.Symbol (literal, _) ->
        let attrs =
          (RenderingAttrs.symbol_attributes `MathML)
          @ make_href xmlattrs xref
        in
        Mpres.Mo (attrs, to_unicode literal)
    | A.Ident (literal, subst)
    | A.Uri (literal, subst) ->
        let attrs =
          (RenderingAttrs.ident_attributes `MathML)
          @ make_href xmlattrs xref
        in
        let name = Mpres.Mi (attrs, to_unicode literal) in
        (match subst with
        | Some []
        | None -> name
        | Some substs ->
            let substs' =
              box_of mathonly (A.H, false, false) []
                (open_brace
                :: (NotationUtil.dress semicolon
                    (List.map
                      (fun (name, t) ->
                        box_of mathonly (A.H, false, false) [] [
                          Mpres.Mi ([], name);
                          Mpres.Mo ([], to_unicode "\\def");
                          aux [] mathonly xref  prec t ])
                      substs))
                @ [ closed_brace ])
            in
            let substs_maction = toggle_action [ hidden_substs; substs' ] in
            box_of mathonly (A.H, false, false) [] [ name; substs_maction ])
    | A.Meta(n, l) ->
        let local_context l =
          box_of mathonly (A.H, false, false) []
            ([ Mpres.Mtext ([], "[") ] @ 
            (NotationUtil.dress (Mpres.Mtext ([],  ";"))
              (List.map 
                (function 
                | None -> Mpres.Mtext ([],  "_")
                | Some t -> aux xmlattrs mathonly xref  prec t) l)) @
             [ Mpres.Mtext ([], "]")])
        in
        let lctxt_maction = toggle_action [ hidden_lctxt; local_context l ] in
        box_of mathonly (A.H, false, false) []
          ([Mpres.Mtext ([], "?"^string_of_int n) ] 
            @ (if l <> [] then [lctxt_maction] else []))
    | A.Literal l -> aux_literal xmlattrs xref prec l
    | A.UserInput -> Mpres.Mtext ([], "%")
    | A.Layout l -> aux_layout mathonly xref  prec l
    | A.Magic _
    | A.Variable _ -> assert false  (* should have been instantiated *)
    | t ->
        prerr_endline ("unexpected ast: " ^ NotationPp.pp_term status t);
        assert false
  and aux_attributes xmlattrs mathonly xref  prec t =
    let reset = ref false in
    let inferred_level = ref None in
    let expected_level = ref None in
    let new_xref = ref [] in
    let new_xmlattrs = ref [] in
    let rec aux_attribute =
      function
      | A.AttributedTerm (attr, t) ->
          (match attr with
          | `Loc _
          | `Raw _ -> ()
          | `Level (-1) -> reset := true
          | `Level child_prec ->
(*               assert (!expected_level = None); *)
              expected_level := !inferred_level;
              inferred_level := Some child_prec
          | `IdRef xref -> new_xref := xref :: !new_xref
          | `XmlAttrs attrs -> new_xmlattrs := attrs @ !new_xmlattrs);
          aux_attribute t
      | t ->
          let prec = 
            match !expected_level with
            | None -> prec
            | Some prec -> prec
          in
          (match !inferred_level with
          | None -> aux !new_xmlattrs mathonly new_xref prec t
          | Some child_prec ->
              let t' = aux !new_xmlattrs mathonly new_xref child_prec t in
              (*prerr_endline 
                ("inferred: "^string_of_int child_prec^ 
                 " exp: "^string_of_int prec ^ 
                 " term: "^BoxPp.render_to_string ~map_unicode_to_tex:false
                    (function x::_->x|_->assert false) 80 t');*)
              if !reset
              then ((*prerr_endline "reset";*)t')
              else add_parens child_prec prec t')
    in
(*     prerr_endline (NotationPp.pp_term t); *)
    aux_attribute t
  and aux_literal xmlattrs xref prec l =
    let attrs = make_href xmlattrs xref in
    (match l with
    | `Symbol s -> Mpres.Mo (attrs, to_unicode s)
    | `Keyword s -> Mpres.Mtext (attrs, to_unicode s)
    | `Number s  -> Mpres.Mn (attrs, to_unicode s))
  and aux_layout mathonly xref  prec l =
    let attrs = make_xref xref in
    let invoke' t = aux [] true (ref [])  prec t in
      (* use the one below to reset precedence and associativity *)
    let invoke_reinit t = aux [] mathonly xref ~-1 t in
    match l with
    | A.Sup (A.Layout (A.Sub (t1,t2)), t3)
    | A.Sup (A.AttributedTerm (_,A.Layout (A.Sub (t1,t2))), t3)
      -> Mpres.Msubsup (attrs, invoke' t1, invoke_reinit t2, invoke_reinit t3)
    | A.Sub (t1, t2) -> Mpres.Msub (attrs, invoke' t1, invoke_reinit t2)
    | A.Sup (t1, t2) -> Mpres.Msup (attrs, invoke' t1, invoke_reinit t2)
    | A.Below (t1, t2) -> Mpres.Munder (attrs, invoke' t1, invoke_reinit t2)
    | A.Above (t1, t2) -> Mpres.Mover (attrs, invoke' t1, invoke_reinit t2)
    | A.Frac (t1, t2)
    | A.Over (t1, t2) ->
        Mpres.Mfrac (attrs, invoke_reinit t1, invoke_reinit t2)
    | A.Atop (t1, t2) ->
        Mpres.Mfrac (atop_attributes @ attrs, invoke_reinit t1,
          invoke_reinit t2)
    | A.InfRule (t1, t2, t3) ->
      Mpres.Mstyle ([None,"mathsize","big"],
       Mpres.Mrow (attrs,
        [Mpres.Mfrac ([],
           Mpres.Mstyle ([None,"scriptlevel","0"],invoke_reinit t1),
           Mpres.Mstyle ([None,"scriptlevel","0"],invoke_reinit t2));
          Mpres.Mstyle ([None,"scriptlevel","2"],
           Mpresentation.Mspace 
            (RenderingAttrs.small_skip_attributes `MathML));
         Mpres.Mstyle ([None,"scriptlevel","1"],invoke_reinit t3)]))
    | A.Sqrt t -> Mpres.Msqrt (attrs, invoke_reinit t)
    | A.Root (t1, t2) ->
        Mpres.Mroot (attrs, invoke_reinit t1, invoke_reinit t2)
    | A.Box ((_, spacing, _) as kind, terms) ->
        let children =
          aux_children mathonly spacing xref  prec
            (NotationUtil.ungroup terms)
        in
        box_of mathonly kind attrs children
    | A.Mstyle (l,terms) -> 
        Mpres.Mstyle 
          (List.map (fun (k,v) -> None,k,v) l, 
           box_of mathonly (A.H, false, false) attrs 
            (aux_children mathonly false xref  prec 
              (NotationUtil.ungroup terms)))
    | A.Mpadded (l,terms) -> 
        Mpres.Mpadded 
          (List.map (fun (k,v) -> None,k,v) l, 
           box_of mathonly (A.H, false, false) attrs 
            (aux_children mathonly false xref  prec 
              (NotationUtil.ungroup terms)))
    | A.Maction alternatives -> 
         toggle_action (List.map invoke_reinit alternatives)
    | A.Group terms ->
	let children =
          aux_children mathonly false xref  prec
            (NotationUtil.ungroup terms)
        in
        box_of mathonly (A.H, false, false) attrs children
    | A.Break -> assert false (* TODO? *)
  and aux_children mathonly spacing xref  prec terms =
    let find_clusters =
      let rec aux_list first clusters acc =
	function
	    [] when acc = [] -> List.rev clusters
	  | [] -> aux_list first (List.rev acc :: clusters) [] []
	  | (A.Layout A.Break) :: tl when acc = [] ->
              aux_list first clusters [] tl
	  | (A.Layout A.Break) :: tl ->
              aux_list first (List.rev acc :: clusters) [] tl
	  | [hd] ->
		aux_list false clusters
                  (aux [] mathonly xref  prec hd :: acc) []
	  | hd :: tl ->
		aux_list false clusters
                  (aux [] mathonly xref  prec hd :: acc) tl
      in
	aux_list true [] []
    in
    let boxify_pres =
      function
	  [t] -> t
	| tl -> box_of mathonly (A.H, spacing, false) [] tl
    in
      List.map boxify_pres (find_clusters terms)
  in
  aux [] false (ref []) prec

let rec print_box (t: boxml_markup) =
  Box.box2xml print_mpres t
and print_mpres (t: mathml_markup) =
  Mpresentation.print_mpres print_box t

let print_xml = print_mpres

(* let render_to_boxml id_to_uri t =
  let xml_stream = print_box (box_of_mpres (render id_to_uri t)) in
  Xml.add_xml_declaration xml_stream *)

