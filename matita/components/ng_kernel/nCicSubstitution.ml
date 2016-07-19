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

(* $Id: nCicSubstitution.ml 11172 2011-01-11 21:06:37Z sacerdot $ *)

module C = NCic 
module Ref = NReference

let debug_print = fun _ -> ();;

let lift_from status ?(no_implicit=true) k n =
 let rec liftaux k = function
    | C.Rel m as t -> if m < k then t else C.Rel (m + n)
    | C.Meta (i,(m,(C.Irl 0 as l))) when k <= m+1 -> C.Meta (i,(m,l))
    | C.Meta (i,(m,l)) when k <= m+1 -> C.Meta (i,(m+n,l))
    | C.Meta (_,(m,C.Irl l)) as t when k > l + m -> t
    | C.Meta (i,(m,l)) -> 
       let lctx = NCicUtils.expand_local_context l in
       C.Meta (i, (m, C.Ctx (HExtlib.sharing_map (liftaux (k-m)) lctx)))
    | C.Implicit _ as t -> (* was the identity *) 
	if no_implicit then assert false
	else t
    | t -> NCicUtils.map status (fun _ k -> k + 1) k liftaux t
 in
 liftaux k
;;

let lift status ?(from=1) ?(no_implicit=true) n t =
  if n = 0 then t else lift_from status ~no_implicit from n t
;;


(* subst t1 t2                                                          *)
(*  substitutes [t1] for [Rel 1] in [t2]                                *)
(*  if avoid_beta_redexes is true (default: false) no new beta redexes  *)
(*  are generated. WARNING: the substitution can diverge when t2 is not *)
(*  well typed and avoid_beta_redexes is true.                          *)
(*  map_arg is ReductionStrategy.from_env_for_unwind when psubst is     *)
(*  used to implement nCicReduction.unwind'                             *)
let rec psubst status ?(avoid_beta_redexes=false) ?(no_implicit=true) map_arg args = 
 let nargs = List.length args in
 let rec substaux k = function
   | C.Rel n as t ->
      (match n with
      | n when n >= (k+nargs) ->
         if nargs <> 0 then C.Rel (n - nargs) else t
      | n when n < k -> t
      | n (* k <= n < k+nargs *) ->
       (try lift status ~no_implicit (k-1) (map_arg (List.nth args (n-k)))
        with Failure _ | Invalid_argument _ -> assert false))
   | C.Meta (i,(m,l)) as t when m >= k + nargs - 1 -> 
       if nargs <> 0 then C.Meta (i,(m-nargs,l)) else t
   | C.Meta (_,(m,(C.Irl l))) as t when k > l + m -> t
   | C.Meta (i,(m,l)) -> 
      let lctx = NCicUtils.expand_local_context l in
       C.Meta (i,(0, 
         C.Ctx (HExtlib.sharing_map 
		  (fun x -> substaux k (lift status ~no_implicit m x)) lctx)))
   | C.Implicit _ as t -> 
       if no_implicit then assert false (* was identity *)
       else t
   | C.Appl (he::tl) as t ->
      (* Invariant: no Appl applied to another Appl *)
      let rec avoid he' = function
        | [] -> he'
        | arg::tl' as args->
            (match he' with
            | C.Appl l -> C.Appl (l@args)
            | C.Lambda (_,_,bo) when avoid_beta_redexes ->
                (* map_arg is here \x.x, Obj magic is needed because 
                 * we don't have polymorphic recursion w/o records *)
                avoid (psubst status
                  ~avoid_beta_redexes ~no_implicit
		  Obj.magic [Obj.magic arg] bo) tl'
            | _ -> if he == he' && args == tl then t else C.Appl (he'::args))
      in
      let tl = HExtlib.sharing_map (substaux k) tl in
      avoid (substaux k he) tl
   | t -> NCicUtils.map status (fun _ k -> k + 1) k substaux t
 in
  substaux 1
;;

let subst status ?avoid_beta_redexes ?no_implicit arg = 
  psubst status ?avoid_beta_redexes ?no_implicit(fun x -> x)[arg];;

(* subst_meta (n, C.Ctx [t_1 ; ... ; t_n]) t                                 *)
(*  returns the term [t] where [Rel i] is substituted with [t_i] lifted by n *)
(*  [t_i] is lifted as usual when it crosses an abstraction                  *)
(* subst_meta (n, (C.Irl _ | C.Ctx [])) t | -> lift status n t               *)
let subst_meta status = function 
  | m, C.Irl _ 
  | m, C.Ctx [] -> lift status m 
  | m, C.Ctx l  -> psubst status (lift status m) l 
;;
