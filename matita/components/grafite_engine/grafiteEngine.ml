(* Copyright (C) 2005, HELM Team.
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

(* $Id: grafiteEngine.ml 13176 2016-04-18 15:29:33Z fguidi $ *)

(* mo file name, ma file name *)
exception NMacro of GrafiteAst.loc * GrafiteAst.nmacro

type 'a disambiguator_input = string * int * 'a

type options = { 
  do_heavy_checks: bool ; 
}

let basic_eval_unification_hint (t,n) status =
 NCicUnifHint.add_user_provided_hint status t n
;;

let inject_unification_hint =
 let basic_eval_unification_hint (t,n) 
   ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
   ~alias_only status
 =
  if not alias_only then
   let t = refresh_uri_in_term (status :> NCic.status) t in
    basic_eval_unification_hint (t,n) status
  else
   status
 in
  GrafiteTypes.Serializer.register#run "unification_hints"
   basic_eval_unification_hint
;;

let eval_unification_hint status t n = 
 let metasenv,subst,status,t =
  GrafiteDisambiguate.disambiguate_nterm status `XTSort [] [] [] ("",0,t) in
 assert (metasenv=[]);
 let t = NCicUntrusted.apply_subst status subst [] t in
 let status = basic_eval_unification_hint (t,n) status in
  NCicLibrary.dump_obj status (inject_unification_hint (t,n))
;;

let basic_index_obj l (status:#NCic.status) =
  status#set_auto_cache 
    (List.fold_left
      (fun t (ks,v) -> 
         List.fold_left (fun t k ->
           NDiscriminationTree.DiscriminationTree.index t k v)
          t ks) 
    status#auto_cache l) 
;;     

let basic_eval_interpretation ~alias_only (dsc, (symbol, args), cic_appl_pattern) status =
 let status =
  if not alias_only then
   Interpretations.add_interpretation status dsc (symbol, args) cic_appl_pattern
  else
   status
 in
 let mode = GrafiteAst.WithPreferences (*assert false*) in (* MATITA 1.0 VEDI SOTTO *)
 let diff =
  [DisambiguateTypes.Symbol (symbol, 0), GrafiteAst.Symbol_alias (symbol,0,dsc)]
 in
  GrafiteDisambiguate.set_proof_aliases status ~implicit_aliases:false mode diff
;;

let inject_interpretation =
 let basic_eval_interpretation (dsc, (symbol, args), cic_appl_pattern)
   ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
   ~alias_only
 =
  let rec refresh =
   function
      NotationPt.NRefPattern (NReference.Ref (uri,spec)) ->
       NotationPt.NRefPattern
        (NReference.reference_of_spec (NCicLibrary.refresh_uri uri) spec)
    | NotationPt.VarPattern _
    | NotationPt.ImplicitPattern as x -> x
    | NotationPt.ApplPattern l -> NotationPt.ApplPattern (List.map refresh l)
  in
  let cic_appl_pattern = refresh cic_appl_pattern in
   basic_eval_interpretation ~alias_only (dsc, (symbol, args), cic_appl_pattern)
 in
  GrafiteTypes.Serializer.register#run "interpretation"
   basic_eval_interpretation
;;

let eval_interpretation status data= 
 let status = basic_eval_interpretation ~alias_only:false data status in
  NCicLibrary.dump_obj status (inject_interpretation data)
;;

let basic_eval_alias (mode,diff) status =
  GrafiteDisambiguate.set_proof_aliases status ~implicit_aliases:false mode diff
;;

let inject_alias =
 let basic_eval_alias (mode,diff) ~refresh_uri_in_universe ~refresh_uri_in_term
   ~refresh_uri_in_reference ~alias_only =
   basic_eval_alias (mode,diff)
 in
  GrafiteTypes.Serializer.register#run "alias" basic_eval_alias
;;

let eval_alias status data= 
 let status = basic_eval_alias data status in
  NCicLibrary.dump_obj status (inject_alias data)
;;

let basic_eval_input_notation (l1,l2) status =
  GrafiteParser.extend status l1 
   (fun env loc ->
     NotationPt.AttributedTerm
      (`Loc loc,TermContentPres.instantiate_level2 status env l2)) 
;;

let inject_input_notation =
 let basic_eval_input_notation (l1,l2)
  ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
  ~alias_only status
 =
   if not alias_only then
    let l1 =
     CicNotationParser.refresh_uri_in_checked_l1_pattern
      ~refresh_uri_in_term:(refresh_uri_in_term (status:>NCic.status))
      ~refresh_uri_in_reference l1 in
    let l2 = NotationUtil.refresh_uri_in_term
      ~refresh_uri_in_term:(refresh_uri_in_term (status:>NCic.status))
      ~refresh_uri_in_reference l2
    in
     basic_eval_input_notation (l1,l2) status
   else
    status
 in
  GrafiteTypes.Serializer.register#run "input_notation"
   basic_eval_input_notation
;;

let eval_input_notation status data= 
 let status = basic_eval_input_notation data status in
  NCicLibrary.dump_obj status (inject_input_notation data)
;;

let basic_eval_output_notation (l1,l2) status =
 TermContentPres.add_pretty_printer status l2 l1
;;

let inject_output_notation =
 let basic_eval_output_notation (l1,l2)
  ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
  ~alias_only status
 =
  if not alias_only then
   let l1 =
    CicNotationParser.refresh_uri_in_checked_l1_pattern
     ~refresh_uri_in_term:(refresh_uri_in_term (status:>NCic.status))
      ~refresh_uri_in_reference l1 in
   let l2 = NotationUtil.refresh_uri_in_term
     ~refresh_uri_in_term:(refresh_uri_in_term (status:>NCic.status))
      ~refresh_uri_in_reference l2
   in
    basic_eval_output_notation (l1,l2) status
  else
   status
 in
  GrafiteTypes.Serializer.register#run "output_notation"
   basic_eval_output_notation
;;

let eval_output_notation status data= 
 let status = basic_eval_output_notation data status in
  NCicLibrary.dump_obj status (inject_output_notation data)
;;

let record_index_obj = 
 let aux l ~refresh_uri_in_universe 
   ~refresh_uri_in_term ~refresh_uri_in_reference ~alias_only status
 =
  let refresh_uri_in_term = refresh_uri_in_term (status:>NCic.status) in
  if not alias_only then
    basic_index_obj
      (List.map 
        (fun ks,v -> List.map refresh_uri_in_term ks, refresh_uri_in_term v) 
      l) status
  else
   status
 in
  GrafiteTypes.Serializer.register#run "index_obj" aux
;;

let compute_keys status uri height kind = 
 let mk_item ty spec =
   let orig_ty = NTacStatus.mk_cic_term [] ty in
   let status,keys = NnAuto.keys_of_type status orig_ty in
   let keys =  
     List.map 
       (fun t -> 
	  snd (NTacStatus.term_of_cic_term status t (NTacStatus.ctx_of t)))
       keys
   in
   keys,NCic.Const(NReference.reference_of_spec uri spec)
 in
 let data = 
  match kind with
  | NCic.Fixpoint (ind,ifl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,rno,ty,_) i -> 
          if ind then mk_item ty (NReference.Fix (i,rno,height)) 
          else mk_item ty (NReference.CoFix height)) ifl
  | NCic.Inductive (b,lno,itl,_) -> 
     HExtlib.list_mapi 
       (fun (_,_,ty,_) i -> mk_item ty (NReference.Ind (b,i,lno))) itl 
     @
     List.map (fun ((_,_,ty),i,j) -> mk_item ty (NReference.Con (i,j+1,lno)))
       (List.flatten (HExtlib.list_mapi 
         (fun (_,_,_,cl) i -> HExtlib.list_mapi (fun x j-> x,i,j) cl)
         itl))
  | NCic.Constant (_,_,Some _, ty, _) -> 
     [ mk_item ty (NReference.Def height) ]
  | NCic.Constant (_,_,None, ty, _) ->
     [ mk_item ty NReference.Decl ]
 in
  HExtlib.filter_map
   (fun (keys, t) ->
     let keys = List.filter
       (function 
         | (NCic.Meta _) 
         | (NCic.Appl (NCic.Meta _::_)) -> false 
         | _ -> true) 
       keys
     in
     if keys <> [] then 
      begin
        HLog.debug ("Indexing:" ^ 
          status#ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        HLog.debug ("With keys:" ^ String.concat "\n" (List.map (fun t ->
          status#ppterm ~metasenv:[] ~subst:[] ~context:[] t) keys));
        Some (keys,t) 
      end
     else 
      begin
        HLog.debug ("Not indexing:" ^ 
          status#ppterm ~metasenv:[] ~subst:[] ~context:[] t);
        None
      end)
    data
;;

let index_obj_for_auto status (uri, height, _, _, kind) = 
 (*prerr_endline (string_of_int height);*)
  let data = compute_keys status uri height kind in
  let status = basic_index_obj data status in
   NCicLibrary.dump_obj status (record_index_obj data)
;; 

let basic_extract_obj obj status =
 try
  ignore (Helm_registry.get "extract_haskell");
  let status,(msg,infos) = NCicExtraction.haskell_of_obj status obj in
   prerr_endline msg;
   status,infos
 with
    Helm_registry.Key_not_found _ -> status,NCicExtraction.empty_info
  | exn -> prerr_endline ("EXTRACTION FAILURE: " ^ Printexc.to_string exn); assert false
;;

let basic_extract_ocaml_obj obj status =
 try
  let status  = OcamlExtraction.print_ocaml_of_obj status obj in
  let infos,status = status#get_info in
   status,infos
 with
  exn -> prerr_endline ("EXTRACTION FAILURE: " ^ Printexc.to_string exn); assert false
;;

let inject_extract_obj =
 let basic_extract_obj info
   ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
   ~alias_only status
 =
  let info= NCicExtraction.refresh_uri_in_info ~refresh_uri_in_reference info in
   status#set_extraction_db
    (NCicExtraction.register_infos status#extraction_db info)
 in
  GrafiteTypes.Serializer.register#run "extraction" basic_extract_obj
;;

let inject_extract_ocaml_obj =
 let basic_extract_ocaml_obj info
   ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
   ~alias_only status
 =
  let info= OcamlExtractionTable.refresh_uri_in_info ~refresh_uri_in_reference ~refresh_uri:NCicLibrary.refresh_uri info in
   status#set_ocaml_extraction_db
    (OcamlExtractionTable.register_infos status#ocaml_extraction_db info)
 in
  GrafiteTypes.Serializer.register#run "ocaml_extraction" basic_extract_ocaml_obj
;;

let eval_extract_obj status obj = 
 let status,infos = basic_extract_obj obj status in
  NCicLibrary.dump_obj status (inject_extract_obj infos)
;;

let eval_extract_ocaml_obj status obj = 
 let status,infos = basic_extract_ocaml_obj obj status in
  NCicLibrary.dump_obj status (inject_extract_ocaml_obj infos)
;;

(*
module EmptyC = 
  struct
    let metasenv = []
    let subst = []
    let context = []
  end
*)

let index_eq print uri (status:#NCic.status) =
  let eq_status = status#eq_cache in
  let eq_status,clause = NCicParamod.index_obj status eq_status uri in
  if print then
   ((*let module NCicBlob =
    struct
     include NCicBlob.NCicBlob(EmptyC)
     let pp t = status#ppterm ~metasenv:[] ~subst:[] ~context:[] t
    end in
   let module Pp = Pp.Pp(NCicBlob) in*)
   (match clause with
     | Some (*clause*) (_,Terms.Equation (_,_,_,o),_,_) ->
        HLog.debug ("Indexed with orientation: " ^ Pp.string_of_comparison o);
        (*HLog.debug ("Indexed as:" ^ Pp.pp_unit_clause clause)*)
     | _ -> HLog.debug "Not indexed (i.e. pruned)")) ;
  status#set_eq_cache eq_status
;;

let record_index_eq =
 let basic_index_eq uri
   ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference 
   ~alias_only status
   = if not alias_only then index_eq false (NCicLibrary.refresh_uri uri) status 
     else
      status
 in
  GrafiteTypes.Serializer.register#run "index_eq" basic_index_eq
;;

let index_eq_for_auto status uri =
 if NnAuto.is_a_fact_obj status uri then
   let newstatus = index_eq true uri status in
     if newstatus#eq_cache == status#eq_cache then status 
     else
       ((*prerr_endline ("recording " ^ (NUri.string_of_uri uri));*)
        NCicLibrary.dump_obj newstatus (record_index_eq uri))
 else 
   ((*prerr_endline "Not a fact";*)
   status)
;; 

let inject_constraint =
 let basic_eval_add_constraint (acyclic,u1,u2) 
     ~refresh_uri_in_universe ~refresh_uri_in_term ~refresh_uri_in_reference
     ~alias_only status
 =
  if not alias_only then
   let u1 = refresh_uri_in_universe u1 in 
   let u2 = refresh_uri_in_universe u2 in 
    (* NCicLibrary.add_constraint adds the constraint to the NCicEnvironment
     * and also to the storage (for undo/redo). During inclusion of compiled
     * files the storage must not be touched. *)
    NCicEnvironment.add_lt_constraint acyclic u1 u2;
    status
  else
   status
 in
  GrafiteTypes.Serializer.register#run "constraints" basic_eval_add_constraint 
;;

let eval_add_constraint status acyclic u1 u2 = 
 let status = NCicLibrary.add_constraint status acyclic u1 u2 in
  NCicLibrary.dump_obj status (inject_constraint (acyclic,u1,u2))
;;

let eval_ng_tac tac =
 let rec aux f (text, prefix_len, tac) =
  match tac with
  | GrafiteAst.NApply (_loc, t) -> NTactics.apply_tac (text,prefix_len,t) 
  | GrafiteAst.NSmartApply (_loc, t) -> 
      NnAuto.smart_apply_tac (text,prefix_len,t) 
  | GrafiteAst.NAssert (_loc, seqs) ->
     NTactics.assert_tac
      ((List.map
        (function (hyps,concl) ->
          List.map
           (function
              (id,`Decl t) -> id,`Decl (text,prefix_len,t)
             |(id,`Def (b,t))->id,`Def((text,prefix_len,b),(text,prefix_len,t))
           ) hyps,
          (text,prefix_len,concl))
       ) seqs)
  | GrafiteAst.NAuto (_loc, (None,a)) -> 
      NnAuto.auto_tac ~params:(None,a) ?trace_ref:None
  | GrafiteAst.NAuto (_loc, (Some l,a)) ->
      NnAuto.auto_tac
	~params:(Some List.map (fun x -> "",0,x) l,a) ?trace_ref:None
  | GrafiteAst.NBranch _ -> NTactics.branch_tac ~force:false
  | GrafiteAst.NCases (_loc, what, where) ->
      NTactics.cases_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NCase1 (_loc,n) -> NTactics.case1_tac n
  | GrafiteAst.NChange (_loc, pat, ww) -> 
      NTactics.change_tac 
       ~where:(text,prefix_len,pat) ~with_what:(text,prefix_len,ww) 
  | GrafiteAst.NConstructor (_loc,num,args) -> 
     NTactics.constructor_tac 
       ?num ~args:(List.map (fun x -> text,prefix_len,x) args)
  | GrafiteAst.NCut (_loc, t) -> NTactics.cut_tac (text,prefix_len,t) 
(*| GrafiteAst.NDiscriminate (_,what) -> NDestructTac.discriminate_tac ~what:(text,prefix_len,what)
  | GrafiteAst.NSubst (_,what) -> NDestructTac.subst_tac ~what:(text,prefix_len,what)*)
  | GrafiteAst.NClear (_loc, l) -> NTactics.clear_tac l
  | GrafiteAst.NDestruct (_,dom,skip) -> NDestructTac.destruct_tac dom skip
  | GrafiteAst.NDot _ -> NTactics.dot_tac 
  | GrafiteAst.NElim (_loc, what, where) ->
      NTactics.elim_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NFocus (_,l) -> NTactics.focus_tac l
  | GrafiteAst.NGeneralize (_loc, where) -> 
      NTactics.generalize_tac ~where:(text,prefix_len,where)
  | GrafiteAst.NId _ -> (fun x -> x)
  | GrafiteAst.NIntro (_loc,n) -> NTactics.intro_tac n
  | GrafiteAst.NIntros (_loc,ns) -> NTactics.intros_tac ns
  | GrafiteAst.NInversion (_loc, what, where) ->
      NTactics.inversion_tac 
        ~what:(text,prefix_len,what)
        ~where:(text,prefix_len,where)
  | GrafiteAst.NLApply (_loc, t) -> NTactics.lapply_tac (text,prefix_len,t) 
  | GrafiteAst.NLetIn (_loc,where,what,name) ->
      NTactics.letin_tac ~where:(text,prefix_len,where) 
        ~what:(text,prefix_len,what) name
  | GrafiteAst.NMerge _ -> NTactics.merge_tac 
  | GrafiteAst.NPos (_,l) -> NTactics.pos_tac l
  | GrafiteAst.NPosbyname (_,s) -> NTactics.case_tac s
  | GrafiteAst.NReduce (_loc, reduction, where) ->
      NTactics.reduce_tac ~reduction ~where:(text,prefix_len,where)
  | GrafiteAst.NRewrite (_loc,dir,what,where) ->
     NTactics.rewrite_tac ~dir ~what:(text,prefix_len,what)
      ~where:(text,prefix_len,where)
  | GrafiteAst.NSemicolon _ -> fun x -> x
  | GrafiteAst.NShift _ -> NTactics.shift_tac 
  | GrafiteAst.NSkip _ -> NTactics.skip_tac
  | GrafiteAst.NUnfocus _ -> NTactics.unfocus_tac
  | GrafiteAst.NWildcard _ -> NTactics.wildcard_tac 
  | GrafiteAst.NTry (_,tac) -> NTactics.try_tac
      (f f (text, prefix_len, tac))
  | GrafiteAst.NAssumption _ -> NTactics.assumption_tac
  | GrafiteAst.NBlock (_,l) -> 
      NTactics.block_tac (List.map (fun x -> aux f (text,prefix_len,x)) l)
  |GrafiteAst.NRepeat (_,tac) ->
      NTactics.repeat_tac (f f (text, prefix_len, tac))
 in
  aux aux tac (* trick for non uniform recursion call *)
;;
      
let subst_metasenv_and_fix_names status =
  let u,h,metasenv, subst,o = status#obj in
  let o = 
    NCicUntrusted.map_obj_kind ~skip_body:true 
     (NCicUntrusted.apply_subst status subst []) o
  in
   status#set_obj(u,h,NCicUntrusted.apply_subst_metasenv status subst metasenv,subst,o)
;;

let is_proof_irrelevant status context ty =
  match
    NCicReduction.whd status ~subst:[] context
     (NCicTypeChecker.typeof status ~subst:[] ~metasenv:[] context ty)
  with
     NCic.Sort NCic.Prop -> true
   | NCic.Sort _ -> false
   | _ -> assert false
;;

let rec relevance_of status ?(context=[]) ty =
 match NCicReduction.whd status ~subst:[] context ty with
    NCic.Prod (n,s,t) ->
     not (is_proof_irrelevant status context s) ::
      relevance_of status ~context:((n,NCic.Decl s)::context) t
  | _ -> []
;;

let compute_relevance status uri =
 function
    NCic.Constant (_,name,bo,ty,attrs) ->
     let relevance = relevance_of status ty in
      NCic.Constant (relevance,name,bo,ty,attrs)
  | NCic.Fixpoint (ind,funs,attrs) ->
     let funs =
       List.map
       (fun (_,name,recno,ty,bo) ->
         let relevance = relevance_of status ty in
          relevance,name,recno,ty,bo
        ) funs
     in
      NCic.Fixpoint (ind,funs,attrs)
  | NCic.Inductive (ind,leftno,tys,attrs) ->
     let context =
      List.rev_map (fun (_,name,arity,_) -> name,NCic.Decl arity) tys in
     let tysno = List.length tys in
     let tys =
       List.map
        (fun (_,name,arity,cons) ->
         let relevance = relevance_of status arity in
         let cons =
          List.map
           (fun (_,name,ty) ->
             let dety =
               NCicTypeChecker.debruijn status uri tysno ~subst:[] [] ty in
             let relevance = relevance_of status ~context dety in
              relevance,name,ty
           ) cons
         in
          (relevance,name,arity,cons)
        ) tys
     in
      NCic.Inductive (ind,leftno,tys,attrs)
;;

let extract_uris status uris =
 List.fold_left
  (fun status uri ->
    let obj = NCicEnvironment.get_checked_obj status uri in
     let status = eval_extract_obj status obj in
      eval_extract_ocaml_obj status obj
  ) status uris
;;

let rec eval_ncommand ~include_paths opts status (text,prefix_len,cmd) =
  match cmd with
  | GrafiteAst.Include (loc, mode, fname) ->
     let _root, baseuri, fullpath, _rrelpath = 
       Librarian.baseuri_of_script ~include_paths fname in
     let baseuri = NUri.uri_of_string baseuri in
     (* MATITA 1.0: keep WithoutPreferences? *)
     let alias_only = (mode = GrafiteAst.OnlyPreferences) in
     let status =
      GrafiteTypes.Serializer.require
       ~alias_only ~baseuri ~fname:fullpath status in
     OcamlExtraction.print_open status
      (NCicLibrary.get_transitively_included status)
  | GrafiteAst.UnificationHint (loc, t, n) -> eval_unification_hint status t n
  | GrafiteAst.NCoercion (loc, name, compose, None) ->
     let status, t, ty, source, target =
       let o_t = NotationPt.Ident (name,None) in
       let metasenv,subst, status,t =
         GrafiteDisambiguate.disambiguate_nterm 
           status `XTNone [] [] [] ("",0,o_t) in
       assert( metasenv = [] && subst = []);
       let ty = NCicTypeChecker.typeof status [] [] [] t in
       let source, target =
         let clean = function
           | NCic.Appl (NCic.Const _ as r :: l) -> 
               NotationPt.Appl (NotationPt.NCic r ::
                 List.map (fun _ -> NotationPt.Implicit `JustOne)l)
           | NCic.Const _ as r -> NotationPt.NCic r
           | NCic.Sort _ as r -> NotationPt.NCic r (* FG: missing case *)
	   | _ -> assert false
	 in
         let rec aux = function
           | NCic.Prod (_,_, (NCic.Prod _ as rest)) -> aux rest
           | NCic.Prod (name, src, tgt) -> (name, clean src), clean tgt
           | _ -> assert false
	 in
	 aux ty
       in
       status, o_t, NotationPt.NCic ty, source, target
     in
      let cmd = 
       GrafiteAst.NCoercion (loc, name, compose, Some (t, ty, source, target))
      in
      eval_ncommand ~include_paths opts status (text,prefix_len,cmd)
  | GrafiteAst.NCoercion (loc, name, compose, Some (t, ty, source, target)) ->
     let status, composites =
      NCicCoercDeclaration.eval_ncoercion status name compose t ty source
       target in
     let status = extract_uris status composites in
     let mode = GrafiteAst.WithPreferences in (* MATITA 1.0: fixme *)
     let aliases = GrafiteDisambiguate.aliases_for_objs status composites in
      eval_alias status (mode,aliases)
  | GrafiteAst.NQed (loc,index) ->
     if status#ng_mode <> `ProofMode then
      raise (GrafiteTypes.Command_error "Not in proof mode")
     else
      let uri,height,menv,subst,obj_kind = status#obj in
       if menv <> [] then
        raise
         (GrafiteTypes.Command_error"You can't Qed an incomplete theorem")
       else
        let obj_kind =
         NCicUntrusted.map_obj_kind 
          (NCicUntrusted.apply_subst status subst []) obj_kind in
        let height = NCicTypeChecker.height_of_obj_kind status uri [] obj_kind in
        (* fix the height inside the object *)
        let rec fix () = function 
          | NCic.Const (NReference.Ref (u,spec)) when NUri.eq u uri -> 
             NCic.Const (NReference.reference_of_spec u
              (match spec with
              | NReference.Def _ -> NReference.Def height
              | NReference.Fix (i,j,_) -> NReference.Fix(i,j,height)
              | NReference.CoFix i -> NReference.CoFix i
              | NReference.Ind _ | NReference.Con _
              | NReference.Decl as s -> s))
          | t -> NCicUtils.map status (fun _ () -> ()) () fix t
        in
        let obj_kind = 
          match obj_kind with
          | NCic.Fixpoint _ -> 
              NCicUntrusted.map_obj_kind (fix ()) obj_kind 
          | _ -> obj_kind
        in
        let obj_kind = compute_relevance status uri obj_kind in
        let obj = uri,height,[],[],obj_kind in
        let old_status = status in
        let status = NCicLibrary.add_obj status obj in
        let status = eval_extract_obj status obj in
        let status = eval_extract_ocaml_obj status obj in
       (try
        let index_obj = index &&
         match obj_kind with
            NCic.Constant (_,_,_,_,(_,`Example,_))
          | NCic.Fixpoint (_,_,(_,`Example,_)) -> false
          | _ -> true
        in
        let status =
         if index_obj then
          let status = index_obj_for_auto status obj in
           (try index_eq_for_auto status uri
           with
              Sys.Break as exn -> raise exn
            | _ -> status)
         else
          status in
        (* purge tinycals stack *)
        let ninitial_stack = Continuationals.Stack.of_nmetasenv [] in
        let status = status#set_stack ninitial_stack in
(*
	  try 
	    index_eq uri status
	  with _ -> prerr_endline "got an exception"; status
	in *)
(*         prerr_endline (status#ppobj obj); *)
        HLog.message ("New object: " ^ NUri.string_of_uri uri);
       (*prerr_endline (status#ppobj obj);*)
           let boxml = NCicElim.mk_elims status obj in
           let boxml = boxml @ NCicElim.mk_projections status obj in
	   let status = status#set_ng_mode `CommandMode in
           let xxaliases = GrafiteDisambiguate.aliases_for_objs status [uri] in
           let mode = GrafiteAst.WithPreferences in (* MATITA 1.0: fixme *)
           let status = eval_alias status (mode,xxaliases) in
           let status =
            List.fold_left
             (fun status boxml ->
               try
                let nstatus =
                 eval_ncommand ~include_paths opts status
                  ("",0,GrafiteAst.NObj (HExtlib.dummy_floc,boxml,true))
                in
                if nstatus#ng_mode <> `CommandMode then
                  begin
                    (*HLog.warn "error in generating projection/eliminator";*)
                    assert(status#ng_mode = `CommandMode);
                    status
                  end
                else
                  nstatus
               with
               | MultiPassDisambiguator.DisambiguationError _ ->
                  HLog.warn "error in disambiguating projection/eliminator";
                  status
               | NCicTypeChecker.TypeCheckerFailure _ ->
                  HLog.warn "error in typechecking projection/eliminator";
                  status
             ) status boxml in             
           let _,_,_,_,nobj = obj in
           (* attempting to generate an inversion principle on the maximum
            * universe can take a long time to fail: this code removes maximal
            * sorts from the universe list *)
           let universes = NCicEnvironment.get_universes () in
           let max_univ = List.fold_left max [] universes in
           let universes = 
             List.filter (fun x -> NCicEnvironment.universe_lt x max_univ)
               universes
           in
           let status = match nobj with
               NCic.Inductive (is_ind,leftno,itl,_) ->
                 List.fold_left (fun status it ->      
                 (let _,ind_name,ty,cl = it in
                  List.fold_left 
                   (fun status outsort ->
                      let status = status#set_ng_mode `ProofMode in
                      try
                       (let status,invobj =
                         NInversion.mk_inverter 
                          (ind_name ^ "_inv_" ^
                            (snd (NCicElim.ast_of_sort outsort)))
                          is_ind it leftno outsort status status#baseuri in
                       let _,_,menv,_,_ = invobj in
                        (match menv with
                             [] -> eval_ncommand ~include_paths opts status
                                    ("",0,GrafiteAst.NQed (Stdpp.dummy_loc,false))
                           | _ -> status))
                       (* XXX *)
                      with
                         Sys.Break as exn -> raise exn
                       | _ -> (*HLog.warn "error in generating inversion principle"; *)
                                let status = status#set_ng_mode `CommandMode in status)
                  status
                  (NCic.Prop::
                    List.map (fun s -> NCic.Type s) universes))) status itl
              | _ -> status
           in
           let status = match nobj with
               NCic.Inductive (is_ind,leftno,itl,_) ->
                 (* first leibniz *)
                 let status' = List.fold_left
                   (fun status it ->
                      let _,ind_name,ty,cl = it in
                      let status = status#set_ng_mode `ProofMode in
                      try
                       (let status,invobj =
                         NDestructTac.mk_discriminator ~use_jmeq:false
                          (ind_name ^ "_discr")
                          it leftno status status#baseuri in
                       let _,_,menv,_,_ = invobj in
                        (match menv with
                             [] -> eval_ncommand ~include_paths opts status
                                    ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,false))
                           | _ -> status))
                       (* XXX *)
                      with 
                      | NDestructTac.ConstructorTooBig k -> 
                          HLog.warn (Printf.sprintf 
                           "unable to generate leibniz discrimination principle (constructor %s too big)"
                           k);
                           let status = status#set_ng_mode `CommandMode in status
                      | _ -> (*HLog.warn "error in generating discrimination principle"; *)
                                let status = status#set_ng_mode `CommandMode in
                                status)
                  status itl
                in
                (* then JMeq *)
                List.fold_left
                   (fun status it ->
                      let _,ind_name,ty,cl = it in
                      let status = status#set_ng_mode `ProofMode in
                      try
                       (let status,invobj =
                         NDestructTac.mk_discriminator ~use_jmeq:true
                          (ind_name ^ "_jmdiscr")
                          it leftno status status#baseuri in
                       let _,_,menv,_,_ = invobj in
                        (match menv with
                             [] -> eval_ncommand ~include_paths opts status
                                    ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,false))
                           | _ -> status))
                       (* XXX *)
                      with
                         Sys.Break as exn -> raise exn
                       | _ -> (*HLog.warn "error in generating discrimination principle"; *)
                                let status = status#set_ng_mode `CommandMode in
                                status)
                  status' itl
              | _ -> status
           in
           let coercions =
            match obj with
              _,_,_,_,NCic.Inductive
               (true,leftno,[_,_,_,[_,_,_]],(_,`Record fields))
               ->
                HExtlib.filter_map
                 (fun (name,is_coercion,arity) ->
                   if is_coercion then Some(name,leftno,arity) else None) fields
            | _ -> [] in
           let status =
            List.fold_left
             (fun status (name,cpos,arity) ->
               try
                 let metasenv,subst,status,t =
                  GrafiteDisambiguate.disambiguate_nterm status `XTNone [] [] []
                   ("",0,NotationPt.Ident (name,None)) in
                 assert (metasenv = [] && subst = []);
                 let status, nuris = 
                   NCicCoercDeclaration.
                     basic_eval_and_record_ncoercion_from_t_cpos_arity 
                      status (name,true,t,cpos,arity) in
                 let aliases = GrafiteDisambiguate.aliases_for_objs status nuris in
                 let status = extract_uris status nuris in
                  eval_alias status (mode,aliases)
               with MultiPassDisambiguator.DisambiguationError _-> 
                 HLog.warn ("error in generating coercion: "^name);
                 status) 
             status coercions
           in
            status
          with
           exn ->
            NCicLibrary.time_travel old_status;
            raise exn)
  | GrafiteAst.NCopy (log,tgt,src_uri, map) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
       let tgt_uri_ext, old_ok = 
         match NCicEnvironment.get_checked_obj status src_uri with
         | _,_,[],[], (NCic.Inductive _ as ok) -> ".ind", ok
         | _,_,[],[], (NCic.Fixpoint _ as ok) -> ".con", ok
         | _,_,[],[], (NCic.Constant _ as ok) -> ".con", ok
         | _ -> assert false
       in
       let tgt_uri = NUri.uri_of_string (status#baseuri^"/"^tgt^tgt_uri_ext) in
       let map = (src_uri, tgt_uri) :: map in
       let ok = 
         let rec subst () = function
           | NCic.Meta _ -> assert false
           | NCic.Const (NReference.Ref (u,spec)) as t ->
               (try NCic.Const 
                 (NReference.reference_of_spec (List.assoc u map)spec)
               with Not_found -> t)
           | t -> NCicUtils.map status (fun _ _ -> ()) () subst t
         in
         NCicUntrusted.map_obj_kind ~skip_body:false (subst ()) old_ok
       in
       let ninitial_stack = Continuationals.Stack.of_nmetasenv [] in
       let status = status#set_obj (tgt_uri,0,[],[],ok) in
       (*prerr_endline (status#ppobj (tgt_uri,0,[],[],ok));*)
       let status = status#set_stack ninitial_stack in
       let status = subst_metasenv_and_fix_names status in
       let status = status#set_ng_mode `ProofMode in
       eval_ncommand ~include_paths opts status ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,false))
  | GrafiteAst.NObj (loc,obj,index) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let status,obj =
       GrafiteDisambiguate.disambiguate_nobj status
        ~baseuri:status#baseuri (text,prefix_len,obj) in
      let uri,height,nmenv,nsubst,nobj = obj in
      let ninitial_stack = Continuationals.Stack.of_nmetasenv nmenv in
      let status = status#set_obj obj in
      let status = status#set_stack ninitial_stack in
      let status = subst_metasenv_and_fix_names status in
      let status = status#set_ng_mode `ProofMode in
      (match nmenv with
          [] ->
           eval_ncommand ~include_paths opts status
             ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,index))
        | _ -> status)
  | GrafiteAst.NDiscriminator (loc, indty) ->
      if status#ng_mode <> `CommandMode then
        raise (GrafiteTypes.Command_error "Not in command mode")
      else
        let status = status#set_ng_mode `ProofMode in
        let metasenv,subst,status,indty =
          GrafiteDisambiguate.disambiguate_nterm status `XTNone [] [] [] (text,prefix_len,indty) in
        let indtyno, (_,_,tys,_,_),leftno = match indty with
            NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,leftno))) as r) ->
              indtyno, NCicEnvironment.get_checked_indtys status r, leftno
          | _ -> prerr_endline ("engine: indty expected... (fix this error message)"); assert false in
        let (_,ind_name,_,_ as it) = List.nth tys indtyno in
        let status,obj =  
          NDestructTac.mk_discriminator ~use_jmeq:true ~force:true (ind_name ^ "_jmdiscr")
           it leftno status status#baseuri in
        let _,_,menv,_,_ = obj in
          (match menv with
               [] -> eval_ncommand ~include_paths opts status ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,false))
             | _ -> prerr_endline ("Discriminator: non empty metasenv");
                    status)
  | GrafiteAst.NInverter (loc, name, indty, selection, sort) ->
     if status#ng_mode <> `CommandMode then
      raise (GrafiteTypes.Command_error "Not in command mode")
     else
      let metasenv,subst,status,sort = match sort with
        | None -> [],[],status,NCic.Sort NCic.Prop
        | Some s ->
           GrafiteDisambiguate.disambiguate_nterm status `XTSort [] [] []
            (text,prefix_len,s) 
      in
      assert (metasenv = []);
      let sort = NCicReduction.whd status ~subst [] sort in
      let sort =
       match sort with 
          NCic.Sort s -> s
        | _ ->
           raise (Invalid_argument (Printf.sprintf
            "ninverter: found target %s, which is not a sort"
             (status#ppterm ~metasenv ~subst ~context:[] sort))) in
      let status = status#set_ng_mode `ProofMode in
      let metasenv,subst,status,indty =
       GrafiteDisambiguate.disambiguate_nterm status `XTNone [] [] subst
        (text,prefix_len,indty) in
      let indtyno,(_,leftno,tys,_,_) =
       match indty with
          NCic.Const ((NReference.Ref (_,NReference.Ind (_,indtyno,_))) as r) ->
           indtyno, NCicEnvironment.get_checked_indtys status r
        | _ ->
          prerr_endline ("engine: indty ="  ^ status#ppterm ~metasenv:[]
           ~subst:[] ~context:[] indty);
          assert false in
      let it = List.nth tys indtyno in
      let status,obj =
       NInversion.mk_inverter name true it leftno ?selection sort 
        status status#baseuri in
      let _,_,menv,_,_ = obj in
       (match menv with
          [] ->
            eval_ncommand ~include_paths opts status
             ("",0,GrafiteAst.NQed(Stdpp.dummy_loc,false))
        | _ -> assert false)
  | GrafiteAst.NUnivConstraint (loc,acyclic,u1,u2) ->
      eval_add_constraint status acyclic [`Type,u1] [`Type,u2]
  (* ex lexicon commands *)
  | GrafiteAst.Interpretation (loc, dsc, (symbol, args), cic_appl_pattern) ->
     let cic_appl_pattern =
      GrafiteDisambiguate.disambiguate_cic_appl_pattern status args
       cic_appl_pattern
     in
      eval_interpretation status (dsc,(symbol, args),cic_appl_pattern)
  | GrafiteAst.Notation (loc, dir, l1, associativity, precedence, l2) ->
      let l1 = 
        CicNotationParser.check_l1_pattern
         l1 (dir = Some `RightToLeft) precedence associativity
      in
      let status =
        if dir <> Some `RightToLeft then eval_input_notation status (l1,l2)
        else status
      in
       if dir <> Some `LeftToRight then eval_output_notation status (l1,l2)
       else status
  | GrafiteAst.Alias (loc, spec) -> 
     let diff =
      (*CSC: Warning: this code should be factorized with the corresponding
             code in DisambiguatePp *)
      match spec with
      | GrafiteAst.Ident_alias (id,uri) -> 
         [DisambiguateTypes.Id id,spec]
      | GrafiteAst.Symbol_alias (symb, instance, desc) ->
         [DisambiguateTypes.Symbol (symb,instance),spec]
      | GrafiteAst.Number_alias (instance,desc) ->
         [DisambiguateTypes.Num instance,spec]
     in
      let mode = GrafiteAst.WithPreferences in(*assert false in (* VEDI SOPRA *) MATITA 1.0*)
       eval_alias status (mode,diff)
;;

let eval_comment opts status (text,prefix_len,c) = status

let rec eval_executable ~include_paths opts status (text,prefix_len,ex) =
  match ex with
  | GrafiteAst.NTactic (_(*loc*), tacl) ->
      if status#ng_mode <> `ProofMode then
       raise (GrafiteTypes.Command_error "Not in proof mode")
      else
       let status =
        List.fold_left 
          (fun status tac ->
            let time0 = Unix.gettimeofday () in
            let status = eval_ng_tac (text,prefix_len,tac) status in
            let time3 = Unix.gettimeofday () in
            HLog.debug ("... eval_ng_tac done in " ^ string_of_float (time3 -. time0) ^ "s");
            let status = subst_metasenv_and_fix_names status in
            let time3 = Unix.gettimeofday () in
            HLog.debug ("... subst_metasenv_and_fix_names done in " ^ string_of_float (time3 -. time0) ^ "s"); status)
          status tacl
       in
        status
  | GrafiteAst.NCommand (_, cmd) ->
      eval_ncommand ~include_paths opts status (text,prefix_len,cmd)
  | GrafiteAst.NMacro (loc, macro) ->
     raise (NMacro (loc,macro))

and eval_ast ~include_paths ?(do_heavy_checks=false) status (text,prefix_len,st)
=
  let opts = { do_heavy_checks = do_heavy_checks ; } in
  match st with
  | GrafiteAst.Executable (_,ex) ->
     eval_executable ~include_paths opts status (text,prefix_len,ex)
  | GrafiteAst.Comment (_,c) -> 
      eval_comment opts status (text,prefix_len,c) 
;;
