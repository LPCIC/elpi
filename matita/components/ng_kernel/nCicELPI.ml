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

module U   = NUri
module R   = NReference
module C   = NCic
module P   = NCicPp
module E   = NCicEnvironment
module LPA = Elpi_ast
module LPX = Elpi_latex_exporter (* initializes the parser, puah :( *)
module LPP = Elpi_parser
module LPR = Elpi_runtime
module LPC = Elpi_custom (* registers the custom predicates, if we need them *)

(* internals ****************************************************************)

let id x = "u+" ^ x

let univ_of u =
   try Scanf.sscanf (U.string_of_uri u) "cic:/matita/pts/Type%s@.univ" id
   with Scanf.Scan_failure _ | End_of_file -> assert false

let mk_univ s =
   let sort, univ = match s with
      | C.Prop             -> "s+prop", "u+0"
      | C.Type []          -> "s+type", "u+0"
      | C.Type [`Type, u]  -> "s+type", univ_of u
      | C.Type [`CProp, u] -> "s+cprop", univ_of u
      | _                  -> assert false (* for now we process just universes in normal form *)
   in
   LPA.mkApp [LPA.mkCon sort; LPA.mkCon univ]

let mk_nil = LPA.mkNil

let mk_cons v vs = LPA.mkSeq [v; vs]

let mk_lref c i =
   try LPA.mkCon (List.nth c (pred i))
   with Not_found -> assert false

let mk_gref r = LPA.mkCon (R.string_of_reference r)

let mk_sort s = LPA.mkApp [LPA.mkCon "sort"; mk_univ s]

let mk_prod n w t = LPA.mkApp [LPA.mkCon "prod"; w; LPA.mkLam n t]

let mk_abst n w t = LPA.mkApp [LPA.mkCon "abst"; w; LPA.mkLam n t]

let mk_abbr n v w t = LPA.mkApp [LPA.mkCon "abst"; v; w; LPA.mkLam n t]

let mk_appl t vs = LPA.mkApp [LPA.mkCon "appl"; t; vs]

let mk_case w v u ts = LPA.mkApp [LPA.mkCon "case"; w; v; u; ts]

let mk_has_some_sort u = LPA.mkApp [LPA.mkCon "has+sort"; u; LPA.mkFreshUVar ()]

let mk_has_type t u = LPA.mkApp [LPA.mkCon "has+type"; t; u]

(* matita to elpi *)
let rec lp_term c = function
   | C.Meta _
   | C.Implicit _          -> assert false (* for now we process just closed terms *)
   | C.Rel i               -> mk_lref c i
   | C.Const r             -> mk_gref r
   | C.Sort s              -> mk_sort s
   | C.Prod (n, w, t)      -> mk_prod n (lp_term c w) (lp_term (n::c) t)
   | C.Lambda (n, w, t)    -> mk_abst n (lp_term c w) (lp_term (n::c) t)
   | C.LetIn (n, w, v, t)  -> mk_abbr n (lp_term c v) (lp_term c w) (lp_term (n::c) t)
   | C.Appl (t :: vs)      -> mk_appl (lp_term c t) (lp_terms c vs)
   | C.Appl []             -> assert false
   | C.Match (r, u, v, ts) -> mk_case (mk_gref r) (lp_term c v) (lp_term c u) (lp_terms c ts)

and lp_terms c = function
   | []      -> mk_nil
   | v :: vs -> mk_cons (lp_term c v) (lp_terms c vs)

let status = new P.status

let resolve_gref r =
   let R.Ref (_, kind) = r in
   match kind with 
      | R.Decl ->
         let _, _, u, _, _ = E.get_checked_decl status r in
         None, lp_term [] u 
      | R.Def _ ->
         let _, _, t, u, _, _ = E.get_checked_def status r in
         Some (lp_term [] t), lp_term [] u 
      | R.Fix _ -> assert false
      | R.CoFix _ -> assert false
      | R.Ind _   -> assert false
      | R.Con _  -> assert false

let show = LPR.Constants.show

let dummy = LPR.Constants.dummy

let fail () = raise LPR.No_clause

let rec get_constant depth = function
   | LPR.Const c                                                    ->
      show c
   | LPR.UVar ({LPR.contents=t;_},vardepth,args) when t != dummy    ->
      get_constant depth (LPR.deref_uv ~from:vardepth ~to_:depth args t)
   | LPR.AppUVar ({LPR.contents=t;_},vardepth,args) when t != dummy ->
      get_constant depth (LPR.deref_appuv ~from:vardepth ~to_:depth args t)
   | _ -> fail ()

let eqc = LPR.Constants.eqc

let t_step ~depth ~env:_ _ = function
   | [t1; t2] -> 
      let r = R.reference_of_string (get_constant depth t1) in
      begin match resolve_gref r with
          | _, u -> [LPR.App (eqc, t2, [LPR.term_of_ast ~depth u])]
      end
   | _ -> fail ()


(* initialization ***********************************************************)

let _ =
   LPR.register_custom "$t+step" t_step

let filenames = ["kernel_matita.elpi"; "pts_cic.elpi"]

let program = ref (LPR.program_of_ast (LPP.parse_program ~filenames))

(* interface ****************************************************************)

let has_some_sort u =
   let query = mk_has_some_sort (lp_term [] u) in
   LPR.execute_once !program (LPR.query_of_ast !program query)

let has_type t u =
   let query = mk_has_type (lp_term [] t) (lp_term [] u) in
   LPR.execute_once !program (LPR.query_of_ast !program query)
