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

(* $Id: cicUtil.ml 10153 2009-07-28 15:17:51Z sacerdot $ *)

exception Meta_not_found of int
exception Subst_not_found of int

(* syntactic_equality up to the                 *)
(* distinction between fake dependent products  *)
(* and non-dependent products, alfa-conversion  *)
let alpha_equivalence status =
  let rec aux t t' =
   if t = t' then true
   else
    match t,t' with
     | NCic.Prod (_,s,t), NCic.Prod (_,s',t') ->
        aux s s' && aux t t'
     | NCic.Lambda (_,s,t), NCic.Lambda (_,s',t') ->
        aux s s' && aux t t'
     | NCic.LetIn (_,s,ty,t), NCic.LetIn(_,s',ty',t') ->
        aux s s' && aux ty ty' && aux t t'
     | NCic.Appl l, NCic.Appl l' when List.length l = List.length l' ->
        (try
          List.fold_left2
           (fun b t1 t2 -> b && aux t1 t2) true l l'
         with
          Invalid_argument _ -> false)
     | NCic.Const _, NCic.Const _ -> t == t'
     | NCic.Match (it,outt,t,pl), NCic.Match (it',outt',t',pl') ->
        it == it' &&
         aux outt outt' && aux t t' &&
          (try
            List.fold_left2
             (fun b t1 t2 -> b && aux t1 t2) true pl pl'
           with
            Invalid_argument _ -> false)
     | NCic.Meta (n1,(s1, NCic.Irl _)), NCic.Meta (n2,(s2, NCic.Irl _))
        when n1 = n2 && s1 = s2 -> true
     | NCic.Meta (i, (s,lc)), NCic.Meta (i', (s',lc')) ->
        let lc = NCicUtils.expand_local_context lc in
        let lc' = NCicUtils.expand_local_context lc' in
        i = i' &&
        (try
          List.fold_left2
           (fun b xt xt' -> b && aux (NCicSubstitution.lift status s xt) (NCicSubstitution.lift status s' xt'))
           true lc lc'
         with
          Invalid_argument _ -> false)
     | NCic.Appl [_], _ | _, NCic.Appl [_] -> assert false
     | NCic.Sort s, NCic.Sort s' -> s == s'
     | _,_ -> false (* we already know that t != t' *)
  in
   aux
;;

exception WhatAndWithWhatDoNotHaveTheSameLength;;

let replace_lifting status ~equality ~context ~what ~with_what ~where =
  let find_image ctx what t =
   let rec find_image_aux =
    function
       [],[] -> raise Not_found
     | what::tl1,with_what::tl2 ->
        if equality ctx what t then with_what else find_image_aux (tl1,tl2)
     | _,_ -> raise WhatAndWithWhatDoNotHaveTheSameLength
   in
    find_image_aux (what,with_what)
  in
  let add_ctx ctx n s = (n, NCic.Decl s)::ctx in
  let add_ctx1 ctx n s ty = (n, NCic.Def (s,ty))::ctx in
  let rec substaux k ctx what t =
   try
    NCicSubstitution.lift status (k-1) (find_image ctx what t)
   with Not_found ->
    match t with
      NCic.Rel _ as t -> t
    | NCic.Meta (i, (shift,l)) -> 
       let l = NCicUtils.expand_local_context l in
       let l' =
        List.map (fun t -> substaux k ctx what (NCicSubstitution.lift status shift t)) l
       in
        NCic.Meta(i,NCicMetaSubst.pack_lc (0, NCic.Ctx l'))
    | NCic.Sort _ as t -> t
    | NCic.Implicit _ as t -> t
    | NCic.Prod (n,s,t) ->
       NCic.Prod
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (NCicSubstitution.lift status 1) what) t)
    | NCic.Lambda (n,s,t) ->
       NCic.Lambda
        (n, substaux k ctx what s, substaux (k + 1) (add_ctx ctx n s) (List.map (NCicSubstitution.lift status 1) what) t)
    | NCic.LetIn (n,s,ty,t) ->
       NCic.LetIn
        (n, substaux k ctx what s, substaux k ctx what ty, substaux (k + 1) (add_ctx1 ctx n s ty) (List.map (NCicSubstitution.lift status 1) what) t)
    | NCic.Appl (he::tl) ->
       (* Invariant: no Appl applied to another Appl *)
       let tl' = List.map (substaux k ctx what) tl in
        begin
         match substaux k ctx what he with
            NCic.Appl l -> NCic.Appl (l@tl')
          | _ as he' -> NCic.Appl (he'::tl')
        end
    | NCic.Appl _ -> assert false
    | NCic.Const _ as t -> t
    | NCic.Match (it,outt,t,pl) ->
       NCic.Match (it,substaux k ctx what outt, substaux k ctx what t,
        List.map (substaux k ctx what) pl)
 in
(*
  prerr_endline "*** replace lifting -- what:";
  List.iter (fun x -> prerr_endline (NCicPp.ppterm ~metasenv:[] ~subst:[] ~context x)) what;
  prerr_endline "\n*** replace lifting -- with what:";
  List.iter (fun x -> prerr_endline (NCicPp.ppterm ~metasenv:[] ~subst:[] ~context x)) with_what;
  prerr_endline "\n*** replace lifting -- where:";
  prerr_endline (NCicPp.ppterm ~metasenv:[] ~subst:[] ~context where);
*)

  substaux 1 context what where
;;


