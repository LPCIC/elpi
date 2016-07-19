(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: table.ml 14641 2011-11-06 11:59:10Z herbelin $ i*)

open Coq
open Miniml

type info_el =
   TypeInfo of NReference.reference * ml_schema 
 | TermInfo of NReference.reference * ml_decl
 | InductiveInfo of NUri.uri * ml_ind
 | GuessProjectionInfo of NUri.uri * int
 | ConfirmProjectionInfo of NReference.reference
 | RegisterId of string
 | ReferenceNameInfo of NReference.reference * string
 | RegisterModname of string
 | ModnameInfo of string * string

type info = info_el list

type db =
 ml_schema Refmap.t *
 ml_decl Refmap.t *
 ml_ind NUri.UriMap.t *
 int NUri.UriMap.t *
 int Refmap.t *
 Idset.t *
 string Refmap.t *
 ((out_channel * Format.formatter) * (out_channel * Format.formatter)) option *
 Idset.t *
 string Stringmap.t *
 Uriset.t *
 string *
 info

let set_keywords,get_keywords =
 let keywords = ref Idset.empty in
  ((:=) keywords),(fun () -> !keywords)

let preamble = "preamble.ml"
let upreamble = "Preamble"
let empty_info = []
let empty_modset = Idset.add preamble Idset.empty
let empty_db () =
 Refmap.empty,Refmap.empty,NUri.UriMap.empty,NUri.UriMap.empty,Refmap.empty,get_keywords (),Refmap.empty,None,empty_modset,Stringmap.empty,Uriset.empty,"",empty_info

let register_info (dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos) info =
 match info with
    TypeInfo (ref,schema) ->
     Refmap.add ref schema dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | TermInfo (ref,schema) ->
     dbty,Refmap.add ref schema dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | InductiveInfo (uri,ind) ->
     dbty,dbt,NUri.UriMap.add uri ind dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | GuessProjectionInfo (uri,n) ->
     dbty,dbt,dbi,NUri.UriMap.add uri n dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | ConfirmProjectionInfo (NReference.Ref (uri,_) as ref) ->
     (try
       let n = NUri.UriMap.find uri dbgp in
       let dbgp = NUri.UriMap.remove uri dbgp in
        dbty,dbt,dbi,dbgp,Refmap.add ref n dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
      with Not_found -> dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos)
  | RegisterId s ->
     dbty,dbt,dbi,dbgp,dbp,Idset.add s dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | ReferenceNameInfo (ref,name) ->
     dbty,dbt,dbi,dbgp,dbp,dbids,Refmap.add ref name dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos
  | RegisterModname s ->
     dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,Idset.add s dbmn1,dbmn2,dbo,curi,infos
  | ModnameInfo (s,name) ->
     dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,Stringmap.add s name dbmn2,dbo,curi,infos

let add_info_to_db (dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos) info =
 dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,info::infos

let register_and_add_info ?(dummy=false) status info =
 let db = status#ocaml_extraction_db in
 let db = register_info db info in
 let db = if dummy then db else add_info_to_db db info in
  status#set_ocaml_extraction_db db

let register_infos = List.fold_left register_info

let refresh_uri_in_type ~refresh_uri_in_reference =
 let rec aux =
  function
   | Tarr (t1,t2) -> Tarr (aux t1, aux t2)
   | Tglob (r,tl) -> Tglob (refresh_uri_in_reference r, List.map aux tl)
   | Tmeta { id=id; contents=contents } ->
      let contents' =
       match contents with
          None -> None
        | Some typ -> Some (aux typ)
       in
        Tmeta { id=id; contents=contents' }
   | t -> t
 in
  aux

let refresh_uri_in_kind ~refresh_uri_in_reference =
 function
    Singleton
  | Coinductive
  | Standard as k -> k
  | Record rl -> Record (List.map refresh_uri_in_reference rl) 

let refresh_uri_in_packet ~refresh_uri_in_reference
 { ip_reference = r;
   ip_consreferences = rs;
   ip_typename = n;
   ip_consnames = ns;
   ip_logical = l;
   ip_sign = s;
   ip_vars = v;
   ip_types = tys } =
 { ip_reference = refresh_uri_in_reference r;
   ip_consreferences = Array.map refresh_uri_in_reference rs;
   ip_typename = n;
   ip_consnames = ns;
   ip_logical = l;
   ip_sign = s;
   ip_vars = v;
   ip_types = Array.map (List.map (refresh_uri_in_type ~refresh_uri_in_reference)) tys }

let refresh_uri_in_ind ~refresh_uri_in_reference
 {ind_kind=k; ind_nparams=n; ind_packets=pa}
=
 let k = refresh_uri_in_kind ~refresh_uri_in_reference k in
 let pa = Array.map (refresh_uri_in_packet ~refresh_uri_in_reference) pa in
 {ind_kind=k; ind_nparams=n; ind_packets=pa}

let refresh_uri_in_ast ~refresh_uri_in_reference =
 let rec aux =
  function
   | MLapp (t,tl) -> MLapp (aux t, List.map aux tl)
   | MLlam (id,t) -> MLlam (id, aux t)
   | MLletin (id,t1,t2) -> MLletin (id, aux t1, aux t2)
   | MLglob r -> MLglob (refresh_uri_in_reference r)
   | MLcons ({c_kind=ckind; c_typs=ctyps}, r, tl) ->
      let cinfo =
       {c_kind=refresh_uri_in_kind ~refresh_uri_in_reference ckind;
        c_typs=List.map (refresh_uri_in_type ~refresh_uri_in_reference) ctyps}
      in
       MLcons (cinfo, refresh_uri_in_reference r, List.map aux tl)
   | MLcase ({m_kind=k; m_typs=typs; m_same=same},t,ba) ->
      let info =
       {m_kind=refresh_uri_in_kind ~refresh_uri_in_reference k;
        m_typs=List.map (refresh_uri_in_type ~refresh_uri_in_reference) typs;
        m_same=same} in
      let ba =
       Array.map
        (fun (r,il,t) -> refresh_uri_in_reference r,il,aux t) ba in
      MLcase (info,aux t,ba)
   | MLfix (n,ida,ta) -> MLfix (n,ida,Array.map aux ta)
   | MLmagic t -> MLmagic (aux t)
   | MLrel _
   | MLexn _
   | MLdummy
   | MLaxiom as t -> t
 in
  aux

let refresh_uri_in_decl ~refresh_uri_in_reference =
 function
    Dind ind -> Dind (refresh_uri_in_ind ~refresh_uri_in_reference ind)
  | Dtype (ref,il,ty) ->
     Dtype
      (refresh_uri_in_reference ref, il,
       refresh_uri_in_type ~refresh_uri_in_reference ty)
  | Dterm (ref,ast,ty) ->
     Dterm
      (refresh_uri_in_reference ref,
       refresh_uri_in_ast ~refresh_uri_in_reference ast,
       refresh_uri_in_type ~refresh_uri_in_reference ty)
  | Dfix (refa, asta, tya) ->
     Dfix
      (Array.map refresh_uri_in_reference refa,
       Array.map (refresh_uri_in_ast ~refresh_uri_in_reference) asta,
       Array.map (refresh_uri_in_type ~refresh_uri_in_reference) tya)

let refresh_uri_in_info_el ~refresh_uri_in_reference ~refresh_uri =
 function
    TypeInfo (ref,(n,typ)) ->
     TypeInfo
      (refresh_uri_in_reference ref,
       (n,refresh_uri_in_type ~refresh_uri_in_reference typ))
  | TermInfo (ref,decl) ->
     TermInfo
      (refresh_uri_in_reference ref,
       refresh_uri_in_decl ~refresh_uri_in_reference decl)
  | InductiveInfo (uri,ind) ->
     InductiveInfo
      (refresh_uri uri, refresh_uri_in_ind ~refresh_uri_in_reference ind)
  | GuessProjectionInfo (uri,n) ->
     GuessProjectionInfo (refresh_uri uri, n)
  | ConfirmProjectionInfo ref ->
     ConfirmProjectionInfo (refresh_uri_in_reference ref)
  | RegisterId s -> RegisterId s
  | ReferenceNameInfo (ref,name) ->
     ReferenceNameInfo (refresh_uri_in_reference ref,name)
  | RegisterModname s -> RegisterModname s
  | ModnameInfo (s,name) -> ModnameInfo (s,name)

let refresh_uri_in_info ~refresh_uri_in_reference ~refresh_uri infos =
 List.map
  (refresh_uri_in_info_el ~refresh_uri_in_reference ~refresh_uri)
  infos

class type g_status =
 object ('self)
  method ocaml_extraction_db: db
  method get_info: info * 'self
 end

class virtual status =
 object (self)
  inherit NCic.status
  val ocaml_extraction_db = empty_db ()
  method ocaml_extraction_db = ocaml_extraction_db
  method get_info =
   let db1,db2,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos = self#ocaml_extraction_db in
    infos,{< ocaml_extraction_db =
              db1,db2,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,empty_info >}
  method set_ocaml_extraction_db v = {< ocaml_extraction_db = v >}
  method set_ocaml_extraction_status
   : 'status. #g_status as 'status -> 'self
   = fun o -> {< ocaml_extraction_db = o#ocaml_extraction_db >}
 end

let open_file status ~baseuri filename =
 let db1,db2,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,_,infos = status#ocaml_extraction_db in
 assert (ch=None);
 let chml = open_out filename in
 let chml = chml,Format.formatter_of_out_channel chml in
 let chmli = open_out (filename ^ "i") in
 let chmli = chmli,Format.formatter_of_out_channel chmli in
 pp_with (snd chml) (str ("open " ^ upreamble ^ "\n") ++ fnl ());
 pp_with (snd chmli) (str ("open " ^ upreamble ^ "\n") ++ fnl ());
 let db = db1,db2,dbi,dbgp,dbp,dbids,dbrefs,Some (chml,chmli),dbmn1,dbmn2,dbo,baseuri,infos in
 status#set_ocaml_extraction_db db

let close_file status =
 let db1,db2,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos = status#ocaml_extraction_db in
 match ch with
    None -> assert false
  | Some ch ->
     Format.pp_print_flush (snd (fst ch)) ();
     Format.pp_print_flush (snd (snd ch)) ();
     close_out (fst (fst ch));
     close_out (fst (snd ch));
     let ch = None in
     let db = db1,db2,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos in
     status#set_ocaml_extraction_db db

let print_ppcmds status ~in_ml cmds =
 let _,_,_,_,_,_,_,ch,_,_,_,_,_ = status#ocaml_extraction_db in
 match ch with
    None -> assert false
  | Some ch ->
     let ch = if in_ml then fst ch else snd ch in
     pp_with (snd ch) cmds

let to_be_included status uri =
 let dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos =
  status#ocaml_extraction_db
 in
  if Uriset.mem uri dbo then
   status,false
  else
   let dbo = Uriset.add uri dbo in
   let status =
    status#set_ocaml_extraction_db
     (dbty,dbt,dbi,dbgp,dbp,dbids,dbrefs,ch,dbmn1,dbmn2,dbo,curi,infos) in
   status,true

let add_term status ref decl =
 let info = TermInfo (ref,decl) in
  register_and_add_info status info

let lookup_term status ref =
 let _,dbt,_,_,_,_,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  Refmap.find ref dbt

let add_type status ref schema =
 let info = TypeInfo (ref,schema) in
  register_and_add_info status info

let lookup_type status ref =
 let dbty,_,_,_,_,_,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  Refmap.find ref dbty

let add_name_for_reference status ref name =
 let info = ReferenceNameInfo (ref,name) in
  register_and_add_info status info

let name_of_reference status ref =
 let _,_,_,_,_,_,dbrefs,_,_,_,_,_,_ = status#ocaml_extraction_db in
  Refmap.find ref dbrefs

let add_modname_for_filename status ref name =
 let info = ModnameInfo (ref,name) in
  register_and_add_info status info

let modname_of_filename status ref =
 let _,_,_,_,_,_,_,_,_,dbmn2,_,_,_ = status#ocaml_extraction_db in
  Stringmap.find ref dbmn2

let add_global_ids status id =
 let info = RegisterId id in
  register_and_add_info status info

let get_global_ids status =
 let _,_,_,_,_,dbids,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  dbids

let add_modname status id =
 let info = RegisterModname id in
  register_and_add_info status info

let get_modnames status =
 let _,_,_,_,_,_,_,_,dbmn1,_,_,_,_ = status#ocaml_extraction_db in
  dbmn1

let add_ind status ?dummy uri ind =
 let info = InductiveInfo (uri,ind) in
  register_and_add_info ?dummy status info

let lookup_ind status uri =
 let _,_,dbi,_,_,_,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  NUri.UriMap.find uri dbi

let current_baseuri status =
 let _,_,_,_,_,_,_,_,_,_,_,suri,_ = status#ocaml_extraction_db in suri

let guess_projection status ref n =
 let info = GuessProjectionInfo (ref,n) in
  register_and_add_info status info

let confirm_projection status ref =
 let info = ConfirmProjectionInfo ref in
  register_and_add_info status info

let is_projection status ref =
 let _,_,_,_,dbp,_,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  Refmap.mem ref dbp

let projection_arity status ref =
 let _,_,_,_,dbp,_,_,_,_,_,_,_,_ = status#ocaml_extraction_db in
  Refmap.find ref dbp

let type_expand () = true

(*s Extraction Optimize *)

type opt_flag =
    { opt_kill_dum : bool; (* 1 *)
      opt_fix_fun : bool;   (* 2 *)
      opt_case_iot : bool;  (* 4 *)
      opt_case_idr : bool;  (* 8 *)
      opt_case_idg : bool;  (* 16 *)
      opt_case_cst : bool;  (* 32 *)
      opt_case_fun : bool;  (* 64 *)
      opt_case_app : bool;  (* 128 *)
      opt_let_app : bool;   (* 256 *)
      opt_lin_let : bool;   (* 512 *)
      opt_lin_beta : bool } (* 1024 *)

let kth_digit n k = (n land (1 lsl k) <> 0)

let flag_of_int n =
    { opt_kill_dum = kth_digit n 0;
      opt_fix_fun = kth_digit n 1;
      opt_case_iot = kth_digit n 2;
      opt_case_idr = kth_digit n 3;
      opt_case_idg = kth_digit n 4;
      opt_case_cst = kth_digit n 5;
      opt_case_fun = kth_digit n 6;
      opt_case_app = kth_digit n 7;
      opt_let_app = kth_digit n 8;
      opt_lin_let = kth_digit n 9;
      opt_lin_beta = kth_digit n 10 }

(* For the moment, we allow by default everything except :
   - the type-unsafe optimization [opt_case_idg], which anyway
     cannot be activated currently (cf [Mlutil.branch_as_fun])
   - the linear let and beta reduction [opt_lin_let] and [opt_lin_beta]
     (may lead to complexity blow-up, subsumed by finer reductions
      when inlining recursors).
*)

let int_flag_init = 1 + 2 + 4 + 8 (*+ 16*) + 32 + 64 + 128 + 256 (*+ 512 + 1024*)

let opt_flag_ref = ref (flag_of_int int_flag_init)

let optims () = !opt_flag_ref
