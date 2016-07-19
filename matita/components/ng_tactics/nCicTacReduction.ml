(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)
 
let rec normalize status ?(delta=0) ~subst ctx t =
 normalize_machine status ~delta ~subst ctx
  (fst (NCicReduction.reduce_machine status ~delta ~subst ctx (0,[],t,[])))
and normalize_machine status ?(delta=0) ~subst ctx (k,e,t,s) =
 let t = 
   if k = 0 then t
   else
     NCicSubstitution.psubst status ~avoid_beta_redexes:true  
       (fun e -> normalize_machine status ~delta ~subst ctx (NCicReduction.from_env ~delta e)) e t in
 let t =
  match t with
     NCic.Meta (n,(s,lc)) ->
      let l = NCicUtils.expand_local_context lc in
      let l' = List.map (normalize status ~delta ~subst ctx) l in
       if l = l' then t
       else
        NCic.Meta (n,(s,NCic.Ctx l))
   | t -> NCicUtils.map status (fun h ctx -> h::ctx) ctx (normalize status ~delta ~subst) t
 in
 if s = [] then t 
 else
  NCic.Appl
   (t::
    (List.map (fun i -> normalize_machine status ~delta ~subst ctx (NCicReduction.from_stack ~delta i)) s))
;;
