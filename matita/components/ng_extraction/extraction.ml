(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: extraction.ml 14786 2011-12-10 12:55:19Z letouzey $ i*)

open Coq
open Miniml
open OcamlExtractionTable
open Mlutil
open Common

(* A set of all fixpoint functions currently being extracted *)
(*CSC: very imperative, fix/check?*)
let current_fixpoints = ref (None : NUri.uri option)

let whd_betadeltaiota status context t =
 NCicReduction.whd status ~subst:[] context t

let whd_betaiotazeta status context t =
 NCicReduction.whd status ~delta:max_int ~subst:[] context t

let isRel = function NCic.Rel _ -> true | _ -> false

let rec split_all_prods status ~subst context te =
  match NCicReduction.whd status ~subst context te with
   | NCic.Prod (name,so,ta) ->
       split_all_prods status ~subst ((name,(NCic.Decl so))::context) ta
   | _ -> context,te
;;

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n *)
let nb_lam =
  let rec nbrec n =
   function
    | NCic.Lambda (_,_,c) -> nbrec (n+1) c
    | _ -> n
  in
  nbrec 0

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then assert false else
  let rec lamdec_rec l n c =
    if n=0 then l,c
    else match c with
      | NCic.Lambda (x,t,c) -> lamdec_rec ((x,NCic.Decl t)::l) (n-1) c
      | _ -> assert false
  in
  lamdec_rec [] n

let decompose_lam =
  let rec lamdec_rec l =
   function
    | NCic.Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | c                -> l,c
  in
  lamdec_rec []

let splay_prod_n status context n =
  let rec decrec context m ln c = if m = 0 then (ln,c) else
    match whd_betadeltaiota status context c with
      | NCic.Prod (n,a,c0) ->
          decrec ((n,NCic.Decl a)::context)
            (m-1) ((n,NCic.Decl a)::ln) c0
      | _                      -> invalid_arg "splay_prod_n"
  in
  decrec context n []

let splay_prod status context =
  let rec decrec context m c =
    let t = whd_betadeltaiota status context c in
    match t with
      | NCic.Prod (n,a,c0) ->
          decrec ((n,NCic.Decl a)::context) ((n,NCic.Decl a)::m) c0
      | _ -> m,t
  in
  decrec context []

let type_of status context t =
 NCicTypeChecker.typeof status ~subst:[] ~metasenv:[] context t

type sorts_family = InProp | InType

let classify_sort =
 function
    NCic.Prop -> InProp
  | NCic.Type u ->
     match NCicEnvironment.family_of u with
        `CProp -> InProp
      | `Type -> InType

let sort_of status context t =
 match
  NCicTypeChecker.typeof status ~subst:[] ~metasenv:[] context t
 with
    NCic.Sort s -> classify_sort s
  | _ -> assert false

(*S Generation of flags and signatures. *)

(* The type [flag] gives us information about any Coq term:
   \begin{itemize}
   \item [TypeScheme] denotes a type scheme, that is
     something that will become a type after enough applications.
     More formally, a type scheme has type $(x_1:X_1)\ldots(x_n:X_n)s$ with
     [s = Set], [Prop] or [Type]
   \item [Default] denotes the other cases. It may be inexact after
     instanciation. For example [(X:Type)X] is [Default] and may give [Set]
     after instanciation, which is rather [TypeScheme]
   \item [Logic] denotes a term of sort [Prop], or a type scheme on sort [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows
     that an [Info] term might in fact be [Logic] later on.
   \end{itemize} *)

type info = Logic | Info

type scheme = TypeScheme | Default

type flag = info * scheme

(*s [flag_of_type] transforms a type [t] into a [flag].
  Really important function. *)

let rec flag_of_type status context t =
  let t = whd_betadeltaiota status context t in
  match t with
    | NCic.Prod (x,t,c) -> flag_of_type status ((x,NCic.Decl t)::context) c
    | NCic.Sort s ->
       (match classify_sort s with
           InProp -> (Logic,TypeScheme)
         | InType -> (Info,TypeScheme))
    | _ ->
      if (sort_of status context t) = InProp then (Logic,Default)
      else (Info,Default)

(*s Two particular cases of [flag_of_type]. *)

let is_default status context t=(flag_of_type status context t= (Info, Default))

exception NotDefault of kill_reason

let check_default status context t =
  match flag_of_type status context t with
    | _,TypeScheme -> raise (NotDefault Ktype)
    | Logic,_ -> raise (NotDefault Kother)
    | _ -> ()

let is_info_scheme status context t =
 (flag_of_type status context t = (Info, TypeScheme))

(*s [type_sign] generates a signature aimed at treating a type application. *)

let rec type_sign status context c =
  match whd_betadeltaiota status context c with
    | NCic.Prod (n,t,d) ->
        (if is_info_scheme status context t then Keep else Kill Kother)
        :: (type_sign status ((n,NCic.Decl t)::context) d)
    | _ -> []

let rec type_scheme_nb_args status context c =
  match whd_betadeltaiota status context c with
    | NCic.Prod (n,t,d) ->
        let n = type_scheme_nb_args status ((n,NCic.Decl t)::context) d in
        if is_info_scheme status context t then n+1 else n
    | _ -> 0

(*CSC: only useful for inline extraction
let _ = register_type_scheme_nb_args type_scheme_nb_args
*)

(*s [type_sign_vl] does the same, plus a type var list. *)

let rec type_sign_vl status context c =
  match whd_betadeltaiota status context c with
    | NCic.Prod (n,t,d) ->
        let s,vl = type_sign_vl status ((n,NCic.Decl t)::context) d in
        if not (is_info_scheme status context t) then Kill Kother::s, vl
        else Keep::s, (next_ident_away (id_of_name n) vl) :: vl
    | _ -> [],[]

let rec nb_default_params status context c =
  match whd_betadeltaiota status context c with
    | NCic.Prod (n,t,d) ->
        let n = nb_default_params status ((n,NCic.Decl t)::context) d in
        if is_default status context t then n+1 else n
    | _ -> 0

(* Enriching a signature with implicit information *)

let sign_with_implicits _r s =
  let implicits = [](*CSC: implicits_of_global r*) in
  let rec add_impl i = function
    | [] -> []
    | sign::s ->
        let sign' =
          if sign = Keep && List.mem i implicits then Kill Kother else sign
        in sign' :: add_impl (succ i) s
  in
  add_impl 1 s

(* Enriching a exception message *)

let rec handle_exn _r _n _fn_name = function x -> x
(*CSC: only for pretty printing
  | MLexn s ->
      (try Scanf.sscanf s "UNBOUND %d"
         (fun i ->
            assert ((0 < i) && (i <= n));
            MLexn ("IMPLICIT "^ msg_non_implicit r (n+1-i) (fn_name i)))
       with _ -> MLexn s)
  | a -> ast_map (handle_exn r n fn_name) a*)

(*S Management of type variable contexts. *)

(* A De Bruijn variable context (db) is a context for translating Coq [Rel]
   into ML type [Tvar]. *)

(*s From a type signature toward a type variable context (db). *)

let db_from_sign s =
  let rec make i acc = function
    | [] -> acc
    | Keep :: l -> make (i+1) (i::acc) l
    | Kill _ :: l -> make i (0::acc) l
  in make 1 [] s

(*s Create a type variable context from indications taken from
  an inductive type (see just below). *)

let rec db_from_ind dbmap i =
  if i = 0 then []
  else (try Intmap.find i dbmap with Not_found -> 0)::(db_from_ind dbmap (i-1))

(*s [parse_ind_args] builds a map: [i->j] iff the i-th Coq argument
  of a constructor corresponds to the j-th type var of the ML inductive. *)

(* \begin{itemize}
   \item [si] : signature of the inductive
   \item [i] :  counter of Coq args for [(I args)]
   \item [j] : counter of ML type vars
   \item [relmax] : total args number of the constructor
   \end{itemize} *)

let parse_ind_args si args relmax =
  let rec parse i j = function
    | [] -> Intmap.empty
    | Kill _ :: s -> parse (i+1) j s
    | Keep :: s ->
      (match args.(i-1) with
         | NCic.Rel k -> Intmap.add (relmax+1-k) j (parse (i+1) (j+1) s)
         | _ -> parse (i+1) (j+1) s)
  in parse 1 1 si

(*S Extraction of a type. *)

(* [extract_type env db c args] is used to produce an ML type from the
   coq term [(c args)], which is supposed to be a Coq type. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

(* [j] stands for the next ML type var. [j=0] means we do not
   generate ML type var anymore (in subterms for example). *)


let rec extract_type status context db j c args =
  match whd_betaiotazeta status context c with
    | NCic.Appl (d::args') ->
        (* We just accumulate the arguments. *)
        extract_type status context db j d (args' @ args)
    | NCic.Lambda (_,_,d) ->
        (match args with
           | [] -> assert false (* otherwise the lambda would be reductible. *)
           | a :: args -> extract_type status context db j (NCicSubstitution.subst status a d) args)
    | NCic.Prod (n,t,d) ->
        assert (args = []);
        let context' = (n,NCic.Decl t)::context in
        (match flag_of_type status context t with
           | (Info, Default) ->
               (* Standard case: two [extract_type] ... *)
               let status,mld = extract_type status context' (0::db) j d [] in
               let status,res = expand status mld in
               (match res with
                  | Tdummy d -> status,Tdummy d
                  | _ ->
                    let status,res=extract_type status context db 0 t []  in
                     status,Tarr (res, mld))
           | (Info, TypeScheme) when j > 0 ->
               (* A new type var. *)
               let status,mld=extract_type status context' (j::db) (j+1) d [] in
               let status,res = expand status mld in
               status,
               (match res with
                  | Tdummy d -> Tdummy d
                  | _ -> Tarr (Tdummy Ktype, mld))
           | _,lvl ->
               let status,mld = extract_type status context' (0::db) j d [] in
               let status,res = expand status mld in
               status,
               (match res with
                  | Tdummy d -> Tdummy d
                  | _ ->
                      let reason = if lvl=TypeScheme then Ktype else Kother in
                      Tarr (Tdummy reason, mld)))
    | NCic.Sort _ -> status,Tdummy Ktype (* The two logical cases. *)
    | _ when sort_of status context (NCicUntrusted.mk_appl c args) = InProp ->
       status,Tdummy Kother
    | NCic.Rel n ->
        (match List.nth context (n-1) with
           | (_,NCic.Def (t,_)) -> extract_type status context db j (NCicSubstitution.lift status n t) args
           | _ ->
               (* Asks [db] a translation for [n]. *)
               if n > List.length db then status,Tunknown
               else let n' = List.nth db (n-1) in
               status,if n' = 0 then Tunknown else Tvar n')
    | NCic.Const (NReference.Ref (uri,spec) as r) ->
       (match spec with
           NReference.Decl ->
            let _,_,typ,_,_ = NCicEnvironment.get_checked_decl status r in
            (match flag_of_type status [] typ with
               | (Info, TypeScheme) ->
                  extract_type_app status context db
                   (r, type_sign status [] typ) args
               | _ -> (* only other case here: Info, Default, i.e. not an ML type *)
                   status,Tunknown (* Brutal approximation ... *))
         | NReference.Def _ ->
            let _,_,bo,typ,_,_ = NCicEnvironment.get_checked_def status r in
            (match flag_of_type status [] typ with
               | (Info, TypeScheme) ->
                   let status,mlt =
                    extract_type_app status context db
                     (r, type_sign status [] typ) args in
                   (*CSC: if is_custom r then mlt else*)
                   let newc = NCicUntrusted.mk_appl bo args in
                   let status,mlt' = extract_type status context db j newc [] in
                   (* ML type abbreviations interact badly with Coq *)
                   (* reduction, so [mlt] and [mlt'] might be different: *)
                   (* The more precise is [mlt'], extracted after reduction *)
                   (* The shortest is [mlt], which use abbreviations *)
                   (* If possible, we take [mlt], otherwise [mlt']. *)
                   let status,res1 = expand status mlt in
                   let status,res2 = expand status mlt' in
                   if res1=res2 then status,mlt else status,mlt'
               | _ -> (* only other case here: Info, Default, i.e. not an ML type *)
                      (* We try to reduce. *)
                      let newc = NCicUntrusted.mk_appl bo args in
                      extract_type status context db j newc [])
         | NReference.Fix _ -> status,Tunknown
         | NReference.Con _
         | NReference.CoFix _ -> assert false
         | NReference.Ind (_,i,_) ->
            let status,ind = extract_ind status uri in
            let s = ind.ind_packets.(i).ip_sign in
             extract_type_app status context db (r,s) args)
    | NCic.Match _ -> status,Tunknown
    | _ -> assert false

(*s Auxiliary function dealing with type application.
  Precondition: [r] is a type scheme represented by the signature [s],
  and is completely applied: [List.length args = List.length s]. *)

and extract_type_app status context db (r,s) args =
  let status,ml_args =
    List.fold_right
      (fun (b,c) (status,a) ->
        if b=Keep then
         let p =
          List.length
           (fst (splay_prod status context (type_of status context c))) in
         let db = iterate (fun l -> 0 :: l) p db in
         let status,res = extract_type_scheme status context db c p in
          status,res::a
        else status,a)
      (List.combine s args) (status,[])
  in status, Tglob (r,  ml_args)

(*S Extraction of a type scheme. *)

(* [extract_type_scheme env db c p] works on a Coq term [c] which is
  an informative type scheme. It means that [c] is not a Coq type, but will
  be when applied to sufficiently many arguments ([p] in fact).
  This function decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Coq [Rel] into ML type [Tvar]. *)

and extract_type_scheme status context db c p =
  if p=0 then extract_type status context db 0 c []
  else
    let c = whd_betaiotazeta status context c in
    match c with
      | NCic.Lambda (n,t,d) ->
          extract_type_scheme status((n,NCic.Decl t)::context) db d (p-1)
      | _ ->
          let rels=fst (splay_prod status context (type_of status context c)) in
          let context = rels@context in
          let eta_args = List.rev_map (fun x -> NCic.Rel x) (interval 1 p) in
          extract_type status context db 0 (NCicSubstitution.lift status p c)
           eta_args


(*S Extraction of an inductive type. *)

and extract_ind status uri =
 try
  status,lookup_ind status uri
 with Not_found ->
  let _,_,_,_,obj = NCicEnvironment.get_checked_obj status uri in
  match obj with
     NCic.Inductive (inductive,leftno,types,(_,ind_pragma)) ->
      extract_ind0 status uri inductive ind_pragma leftno types
   | _ -> assert false

and extract_ind0 status uri inductive ind_pragma leftno types =
    (* First, if this inductive is aliased via a Module, *)
    (* we process the original inductive. *)
    (* Everything concerning parameters. *)
    (* We do that first, since they are common to all the [mib]. *)
    let _,_,mipty0,_ = List.hd types in
    let mipcontext,_=NCicReduction.split_prods status ~subst:[] [] ~-1 mipty0 in
    let epar_rev,_= HExtlib.split_nth leftno (List.rev mipcontext) in
    let epar = List.rev epar_rev in
    (* First pass: we store inductive signatures together with *)
    (* their type var list. *)
    let packets =
      Array.mapi
        (fun tyno (_,name,arity,kl) ->
           let _,sort=NCicReduction.split_prods status ~subst:[] [] ~-1 arity in
           let sort=match sort with NCic.Sort sort -> sort | _ ->assert false in
           let b = classify_sort sort <> InProp in
           let s,v = if b then type_sign_vl status [] arity else [],[] in
           let t = Array.make (List.length kl) [] in
           let kl = Array.of_list kl in
           let spec = NReference.Ind (inductive,tyno,leftno) in
           let ref = NReference.reference_of_spec uri spec in
           { ip_reference = ref;
             ip_consreferences =
              Array.mapi
               (fun i _ ->
                 NReference.reference_of_spec uri
                  (NReference.Con (tyno,i+1,leftno))
               ) kl;
             ip_typename = name;
             ip_consnames= Array.map (fun (_,name,_) -> name) kl;
             ip_logical = (not b);
             ip_sign = s;
             ip_vars = v;
             ip_types = t
           })
        (Array.of_list types)
    in
    let status = add_ind ~dummy:true status uri
      {ind_kind = Standard;
       ind_nparams = leftno;
       ind_packets = packets
      } in
    (* Second pass: we extract constructors *)
    let rec aux1 i status =
     if i = List.length types then status
     else begin
      let p = packets.(i) in
      let _,_,_,cl = List.nth types i in
      if not p.ip_logical then
        let ktypes = Array.of_list (List.map (fun (_,_,arity) -> arity) cl) in
        let rec aux2 j status =
         if j = Array.length ktypes then status
         else begin
          let tctx,t =
           NCicReduction.split_prods status ~subst:[] [] leftno ktypes.(j) in
          let prods,head = split_all_prods status ~subst:[] tctx t in
          let nprods = List.length prods in
          let args = match head with
            | NCic.Appl (_f::args) -> Array.of_list args (* [f = Ind ip] *)
            | _ -> [||]
          in
          let dbmap = parse_ind_args p.ip_sign args nprods in
          let db = db_from_ind dbmap leftno in
          let status,res = extract_type_cons status epar db dbmap t (leftno+1)in
          p.ip_types.(j) <- res;
          aux2 (j+1) status
         end
        in
         let status = aux2 0 status in
         aux1 (i+1) status
      else begin
       aux1 (i+1) status
      end
     end in
    let status = aux1 0 status in
    (* Third pass: we determine special cases. *)
    let status,ind_info =
     (*CSC: let ip = (kn, 0) in
     let r = IndRef ip in
     if is_custom r then raise_I status Standard;*)
     if not inductive then status,Coinductive else
     if List.length types <> 1 then status,Standard else
     let p = packets.(0) in
     if p.ip_logical then status,Standard else
     if Array.length p.ip_types <> 1 then status,Standard else
     let typ = p.ip_types.(0) in
     let status,l =
      List.fold_right
       (fun x (status,res) ->
         let status,y = expand status x in
          status,y::res
       ) typ (status,[]) in
     let l = List.filter (fun t -> not (isDummy t)) l in
     if List.length l = 1 && not (type_mem_kn uri (List.hd l))
     then status,Singleton else
     if l = [] then status,Standard else
     (match ind_pragma with
         `Regular -> status,Standard
       | `Record fields ->
           let baseuri = NUri.baseuri_of_uri uri in
           let field_names = List.map (fun (n,_,_) -> n) fields in
           assert (List.length field_names = List.length typ);
           let rec select_fields status l typs = match l,typs with
             | [],[] -> status,[]
             | id::l, typ::typs ->
                let status,res = expand status typ in
                if isDummy res then
                 select_fields status l typs
                else
                 (* Is it safe to use [id] for projections [foo.id] ? *)
                 let status,res = type2signature status typ in
                 let fielduri =
                  NUri.uri_of_string (baseuri ^ "/" ^ id ^ ".con") in
                 let fieldfakeref =
                  NReference.reference_of_spec fielduri fake_spec in
(*
                 let ref =
                  try
                   let fieldspec =
                    let (_,height,_,_,obj) =
                     NCicEnvironment.get_checked_obj status fielduri
                    in
                     match obj with
                        NCic.Fixpoint (_,fs,(_,_,`Projection)) ->
                         let _,_,recparamno,_,_ = List.nth fs 0 in
                         NReference.Fix (0,recparamno,height)
                      | _ -> assert false
                   in
                    NReference.reference_of_spec fielduri fieldspec
                  with NCicEnvironment.ObjectNotFound _ ->
                    assert false
                 in *)
                 let status =
                  if List.for_all ((=) Keep) res
                  then
                   let n = nb_default_params status [] mipty0 in
                    guess_projection status fielduri n
                  else status in
                 let status,res = select_fields status l typs in
                 status, fieldfakeref::res
             | _ -> assert false
           in
           let status,field_glob = select_fields status field_names typ in
           (* Is this record officially declared with its projections ? *)
           (* If so, we use this information. *)
           status, Record field_glob)
    in
    let i = {ind_kind = ind_info;
             ind_nparams = leftno;
             ind_packets = packets
            } in
    let status = add_ind status uri i in
     status,i

(*s [extract_type_cons] extracts the type of an inductive
  constructor toward the corresponding list of ML types.

   - [db] is a context for translating Coq [Rel] into ML type [Tvar]
   - [dbmap] is a translation map (produced by a call to [parse_in_args])
   - [i] is the rank of the current product (initially [params_nb+1])
*)

and extract_type_cons status context db dbmap c i =
  match whd_betadeltaiota status context c with
    | NCic.Prod (n,t,d) ->
        let context' = (n,NCic.Decl t)::context in
        let db' = (try Intmap.find i dbmap with Not_found -> 0) :: db in
        let status,l = extract_type_cons status context' db' dbmap d (i+1) in
        let status, res = extract_type status context db 0 t [] in
        status, res::l
    | _ -> status,[]

(*s Recording the ML type abbreviation of a Coq type scheme constant. *)

and mlt_env status r =
 try
  if false (*CSC:XXX not (visible_con kn)*) then raise Not_found;
  match lookup_term status r with
   | Dtype (_,_vl,mlt) -> Some (status,mlt)
   | _ -> None
 with Not_found ->
  match r with
     NReference.Ref (_,NReference.Def _) ->
      let _,_,body,typ,_,_ = NCicEnvironment.get_checked_def status r in
       (match flag_of_type status [] typ with
          | Info,TypeScheme ->
              let s,vl = type_sign_vl status [] typ in
              let db = db_from_sign s in
              let status,t =
               extract_type_scheme status [] db body (List.length s) in
              let status = add_term status r (Dtype (r, vl, t)) in
               Some (status,t)
          | _ -> None)
   | NReference.Ref (_,NReference.Decl) -> None
   | NReference.Ref (_,NReference.Fix _)
   | NReference.Ref (_,NReference.CoFix _) -> assert false
   | NReference.Ref (_,NReference.Ind _)
   | NReference.Ref (_,NReference.Con _) -> None

and expand status = type_expand status mlt_env
and type2signature status = type_to_signature status mlt_env
let type2sign status = type_to_sign status mlt_env
let type_expunge status = type_expunge status mlt_env
let type_expunge_from_sign status = type_expunge_from_sign status mlt_env

(*s Extraction of the type of a constant. *)

let type_of_constant status (NReference.Ref (uri,spec)) =
 let (_,_,_,_,obj) = NCicEnvironment.get_checked_obj status uri in
 match obj,spec with
    NCic.Constant (_,_,_,typ,_),_ -> typ
  | NCic.Fixpoint (_,fs,_), (NReference.Fix (n,_,_) | NReference.CoFix n) ->
     let _,_,_,typ,_ = List.nth fs n in
      typ
  | _ -> assert false

let record_constant_type status r opt_typ =
  try
(*CSC:XXX to be implemented?    if not (visible_con kn) then raise Not_found;*)
    status,lookup_type status r
  with Not_found ->
    let typ = match opt_typ with
      | None -> type_of_constant status r
      | Some typ -> typ in
    let status,mlt = extract_type status [] [] 1 typ [] in
    let schema = (type_maxvar mlt, mlt) in
    let status = add_type status r schema in
     status,schema

(*S Extraction of a term. *)

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [mle] is a ML environment [Mlenv.t]. *)
(* [mlt] is the ML type we want our extraction of [(c args)] to have. *)

let rec extract_term status context mle mlt c args =
  match c with
      NCic.Appl [] -> assert false
    | NCic.Appl (f::a) ->
        extract_term status context mle mlt f (a@args)
    | NCic.Lambda (n, t, d) ->
        let id = n in
        (match args with
           | a :: l ->
               (* We make as many [LetIn] as possible. *)
                let d' = NCic.LetIn (id,t,a,NCic.Appl (d::(List.map (NCicSubstitution.lift status 1) l)))
               in extract_term status context mle mlt d' []
           | [] ->
               let context' = (id, NCic.Decl t)::context in
               let id, a =
                 try check_default status context t; Id id, new_meta()
                 with NotDefault d -> Dummy, Tdummy d
               in
               let b = new_meta () in
               (* If [mlt] cannot be unified with an arrow type, then magic! *)
               let magic = needs_magic (mlt, Tarr (a, b)) in
               let status,d' =
                extract_term status context' (Mlenv.push_type mle a) b d [] in
               status,put_magic_if magic (MLlam (id, d')))
    | NCic.LetIn (n, t1, c1, c2) ->
        let id = n in
        let context' = (id, NCic.Def (c1, t1))::context in
        let args' = List.map (NCicSubstitution.lift status 1) args in
        (try
          check_default status context t1;
          let a = new_meta () in
          let status,c1' = extract_term status context mle a c1 [] in
          (* The type of [c1'] is generalized and stored in [mle]. *)
          let mle' =
            if generalizable c1'
            then Mlenv.push_gen mle a
            else Mlenv.push_type mle a
          in
          let status,res = extract_term status context' mle' mlt c2 args' in
          status,MLletin (Id id, c1', res)
        with NotDefault d ->
          let mle' = Mlenv.push_std_type mle (Tdummy d) in
          let status,res = extract_term status context' mle' mlt c2 args' in
          status,ast_pop res)
    | NCic.Const ((NReference.Ref (uri,
       ( NReference.Decl
       | NReference.Def _
       | NReference.Fix _
       | NReference.CoFix _ ))) as ref) ->
        extract_cst_app status context mle mlt uri ref args
    | NCic.Const ((NReference.Ref (_,(NReference.Con _))) as ref) ->
        extract_cons_app status context mle mlt ref args
    | NCic.Rel n ->
        (* As soon as the expected [mlt] for the head is known, *)
        (* we unify it with an fresh copy of the stored type of [Rel n]. *)
        let extract_rel status mlt =
         status,put_magic (mlt, Mlenv.get mle n) (MLrel n)
        in extract_app status context mle mlt extract_rel args
    | NCic.Match (ref,_,c0,br) ->
         extract_app status context mle mlt
         (extract_case context mle (ref,c0,Array.of_list br)) args
    | NCic.Const (NReference.Ref (_,NReference.Ind _))
    | NCic.Prod _
    | NCic.Sort _
    | NCic.Implicit _
    | NCic.Meta _ -> assert false

(*s [extract_maybe_term] is [extract_term] for usual terms, else [MLdummy] *)

and extract_maybe_term status context mle mlt c =
  try check_default status context (type_of status context c);
    extract_term status context mle mlt c []
  with NotDefault d ->
    status,put_magic (mlt, Tdummy d) MLdummy

(*s Generic way to deal with an application. *)

(* We first type all arguments starting with unknown meta types.
   This gives us the expected type of the head. Then we use the
   [mk_head] to produce the ML head from this type. *)

and extract_app status context mle mlt mk_head args =
  let metas = List.map new_meta args in
  let type_head = type_recomp (metas, mlt) in
  let status,mlargs =
   List.fold_right2
    (fun x y (status,res) ->
      let status,z = extract_maybe_term status context mle x y in
       status,z::res
    ) metas args (status,[]) in
  let status,res = mk_head status type_head in
  status,mlapp res mlargs

(*s Auxiliary function used to extract arguments of constant or constructor. *)

and make_mlargs status context e s args typs =
  let rec f status = function
    | [], [], _ -> status,[]
    | a::la, t::lt, [] ->
       let status,res = extract_maybe_term status context e t a in
       let status,res2 = f status (la,lt,[]) in
       status, res :: res2
    | a::la, t::lt, Keep::s ->
       let status,res = extract_maybe_term status context e t a in
       let status,res2 = f status (la,lt,s) in
        status, res :: res2
    | _::la, _::lt, _::s -> f status (la,lt,s)
    | _ -> assert false
  in f status (args,typs,s)

(*s Extraction of a constant applied to arguments. *)

and extract_cst_app status context mle mlt uri ref args =
  (* First, the [ml_schema] of the constant, in expanded version. *)
  let status,(nb,t) = record_constant_type status ref None in
  let status,res = expand status t in
  let schema = nb, res in
  (* Can we instantiate types variables for this constant ? *)
  (* In Ocaml, inside the definition of this constant, the answer is no. *)
  let instantiated =
    if
     match !current_fixpoints with None -> false | Some uri' -> NUri.eq uri uri'
    then var2var' (snd schema)
    else instantiation schema
  in
  (* Then the expected type of this constant. *)
  let a = new_meta () in
  (* We compare stored and expected types in two steps. *)
  (* First, can [kn] be applied to all args ? *)
  let metas = List.map new_meta args in
  let magic1 = needs_magic (type_recomp (metas, a), instantiated) in
  (* Second, is the resulting type compatible with the expected type [mlt] ? *)
  let magic2 = needs_magic (a, mlt) in
  (* The internal head receives a magic if [magic1] *)
  let head = put_magic_if magic1 (MLglob ref) in
  (* Now, the extraction of the arguments. *)
  let status,s_full = type2signature status (snd schema) in
  let s_full = sign_with_implicits ref s_full in
  let s = sign_no_final_keeps s_full in
  let ls = List.length s in
  let la = List.length args in
  (* The ml arguments, already expunged from known logical ones *)
  let status,mla = make_mlargs status context mle s args metas in
  let mla =
    if not magic1 then
      try
        let l,l' = list_chop (projection_arity status ref) mla in
        if l' <> [] then (List.map (fun _ -> MLexn "Proj Args") l) @ l'
        else mla
      with _ -> mla
    else mla
  in
  (* For strict languages, purely logical signatures with at least
     one [Kill Kother] lead to a dummy lam. So a [MLdummy] is left
     accordingly. *)
  let optdummy = match sign_kind s_full with
    | UnsafeLogicalSig -> [MLdummy]
    | _ -> []
  in
  (* Different situations depending of the number of arguments: *)
  if la >= ls
  then
    (* Enough args, cleanup already done in [mla], we only add the
       additionnal dummy if needed. *)
    status,put_magic_if (magic2 && not magic1) (mlapp head (optdummy @ mla))
  else
    (* Partially applied function with some logical arg missing.
       We complete via eta and expunge logical args. *)
    let ls' = ls-la in
    let s' = list_skipn la s in
    let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
    let e = anonym_or_dummy_lams (mlapp head mla) s' in
    status,put_magic_if magic2 (remove_n_lams (List.length optdummy) e)

(*s Extraction of an inductive constructor applied to arguments. *)

(* \begin{itemize}
   \item In ML, contructor arguments are uncurryfied.
   \item We managed to suppress logical parts inside inductive definitions,
   but they must appears outside (for partial applications for instance)
   \item We also suppressed all Coq parameters to the inductives, since
   they are fixed, and thus are not used for the computation.
   \end{itemize} *)

and extract_cons_app status context mle mlt ref (*(((kn,i) as ip,j) as cp)*) args =
  let uri,i,j =
   match ref with
      NReference.Ref (uri,NReference.Con(i,j,_)) -> uri,i,j
    | _ -> assert false in
  let b,_,_,_,_ = NCicEnvironment.get_checked_indtys status ref in
  let tyref = NReference.mk_indty b ref in
  (* First, we build the type of the constructor, stored in small pieces. *)
  let status,mi = extract_ind status uri in
  let params_nb = mi.ind_nparams in
  let oi = mi.ind_packets.(i) in
  let nb_tvars = List.length oi.ip_vars in
  let status,types =
   List.fold_right
    (fun x (status,res) ->
      let status,y = expand status x in
       status,y::res
    ) oi.ip_types.(j-1) (status,[]) in
  let list_tvar = List.map (fun i -> Tvar i) (interval 1 nb_tvars) in
  let type_cons = type_recomp (types, Tglob (tyref, list_tvar)) in
  let type_cons = instantiation (nb_tvars, type_cons) in
  (* Then, the usual variables [s], [ls], [la], ... *)
  let status,s =
   List.fold_right
    (fun x (status,res) ->
      let status,y = type2sign status x in
       status,y::res)
    types (status,[]) in
  let s = sign_with_implicits ref s in
  let ls = List.length s in
  let la = List.length args in
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in
  let args' = list_lastn la' args in
  (* Now, we build the expected type of the constructor *)
  let metas = List.map new_meta args' in
  (* If stored and expected types differ, then magic! *)
  let a = new_meta () in
  let magic1 = needs_magic (type_cons, type_recomp (metas, a)) in
  let magic2 = needs_magic (a, mlt) in
  let head status mla =
    if mi.ind_kind = Singleton then
      status, put_magic_if magic1 (List.hd mla)
    else
      let status,typeargs = match snd (type_decomp type_cons) with
        | Tglob (_,l) ->
           List.fold_right
            (fun x (status,res) ->
              let status,y = type_simpl status x in
               status,y::res)
            l (status,[])
        | _ -> assert false
      in
      let info = {c_kind = mi.ind_kind; c_typs = typeargs} in
      status, put_magic_if magic1 (MLcons (info, ref, mla))
  in
  (* Different situations depending of the number of arguments: *)
  if la < params_nb then
    let status,head' = head status (eta_args_sign ls s) in
    status,
    put_magic_if magic2
      (dummy_lams (anonym_or_dummy_lams head' s) (params_nb - la))
  else
    let status,mla = make_mlargs status context mle s args' metas in
    if la = ls + params_nb
    then
     let status,res = head status mla in
      status,put_magic_if (magic2 && not magic1) res
    else (* [ params_nb <= la <= ls + params_nb ] *)
      let ls' = params_nb + ls - la in
      let s' = list_lastn ls' s in
      let mla = (List.map (ast_lift ls') mla) @ (eta_args_sign ls' s') in
      let status,res = head status mla in
       status,put_magic_if magic2 (anonym_or_dummy_lams res s')

(*S Extraction of a case. *)

and extract_case context mle (ip,c,br) status mlt =
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let uri,i =
   match ip with
      NReference.Ref (uri,NReference.Ind (_,i,_)) -> uri,i
    | _ -> assert false
  in
  let br_size = Array.length br in
  if br_size = 0 then begin
    (*CSC: to be implemented only if we allow inlining of recursors add_recursors env kn; (* May have passed unseen if logical ... *)*)
    status,MLexn "absurd case"
  end else
    (* [c] has an inductive type, and is not a type scheme type. *)
    let t = type_of status context c in
    (* The only non-informative case: [c] is of sort [Prop] *)
    if (sort_of status context t) = InProp then
      begin
        (*CSC: to be implemented only if we allow inlining of recursors add_recursors env kn; (* May have passed unseen if logical ... *)*)
        (* Logical singleton case: *)
        (* [match c with C i j k -> t] becomes [t'] *)
        assert (br_size = 1);
        let ni =
         let _,leftno,tys,_,_ = NCicEnvironment.get_checked_indtys status ip in
         let _,_,_,cl = List.hd tys in
         let _,_,cty = List.hd cl in
         let prods,_ = split_all_prods status ~subst:[] [] cty in
         List.length prods - leftno
        in
        let s = iterate (fun l -> Kill Kother :: l) ni [] in
        let mlt = iterate (fun t -> Tarr (Tdummy Kother, t)) ni mlt in
        let status,e = extract_maybe_term status context mle mlt br.(0) in
        status, snd (case_expunge s e)
      end
    else
      let status,mi = extract_ind status uri in
      let oi = mi.ind_packets.(i) in
      let metas = Array.init (List.length oi.ip_vars) new_meta in
      (* The extraction of the head. *)
      let type_head = Tglob (ip, Array.to_list metas) in
      let status,a = extract_term status context mle type_head c [] in
      (* The extraction of each branch. *)
      let extract_branch status i =
        let r = NReference.mk_constructor (i+1) ip in
        (* The types of the arguments of the corresponding constructor. *)
        let f status t =
         let status,res = expand status t in
         status,type_subst_vect metas res in
        let status,l =
         List.fold_right
          (fun x (status,res) ->
            let status,y = f status x in
             status,y::res)
          oi.ip_types.(i) (status,[]) in
        (* the corresponding signature *)
        let status,s =
         List.fold_right
          (fun x (status,res) ->
            let status,y = type2sign status x in
             status,y::res)
          oi.ip_types.(i) (status,[]) in
        let s = sign_with_implicits r s in
        (* Extraction of the branch (in functional form). *)
        let status,e =
         extract_maybe_term status context mle (type_recomp (l,mlt)) br.(i) in
        (* We suppress dummy arguments according to signature. *)
        let ids,e = case_expunge s e in
        let e' = handle_exn r (List.length s) (fun _ -> "_") e in
        status,(r, List.rev ids, e')
      in
      if mi.ind_kind = Singleton then
        begin
          (* Informative singleton case: *)
          (* [match c with C i -> t] becomes [let i = c' in t'] *)
          assert (br_size = 1);
          let status,(_,ids,e') = extract_branch status 0 in
          assert (List.length ids = 1);
          status,MLletin (tmp_id (List.hd ids),a,e')
        end
      else
        (* Standard case: we apply [extract_branch]. *)
        let status,typs = List.fold_right
         (fun x (status,res) ->
           let status,y = type_simpl status x in
            status,y::res)
         (Array.to_list metas) (status,[]) in
        let info={ m_kind = mi.ind_kind; m_typs = typs; m_same = BranchNone } in
        let status,res =
         array_fold_right_i
          (fun i _ (status,res) ->
            let status,y = extract_branch status i in
             status,y::res) br (status,[])
        in
         status,MLcase (info, a, Array.of_list res)

(*S ML declarations. *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t],
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

let rec decomp_lams_eta_n n m status context c t =
  let rels = fst (splay_prod_n status context n t) in
  let rels',c = decompose_lam c in
  let d = n - m in
  (* we'd better keep rels' as long as possible. *)
  let rels=(list_firstn d rels)@(List.map (fun (n,t) -> n, NCic.Decl t) rels')in
  let eta_args = List.rev_map (fun n -> NCic.Rel n) (interval 1 d) in
  rels, NCic.Appl ((NCicSubstitution.lift status d c)::eta_args)

(* Let's try to identify some situation where extracted code
   will allow generalisation of type variables *)

let rec gentypvar_ok c =
 match c with
  | NCic.Lambda _ -> true
  | NCic.Const (NReference.Ref (_,
     (NReference.Decl
     |NReference.Def _
     |NReference.Fix _
     |NReference.CoFix _))) -> true
  | NCic.Appl (c::v) ->
      (* if all arguments are variables, these variables will
         disappear after extraction (see [empty_s] below) *)
      List.for_all isRel v && gentypvar_ok c
  | _ -> false

(*s From a constant to a ML declaration. *)

let extract_std_constant status uri body typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let status,res = record_constant_type status uri (Some typ) in
  let t = snd res in
  (* The real type [t']: without head products, expanded, *)
  (* and with [Tvar] translated to [Tvar'] (not instantiable). *)
  let status,res = expand status (var2var' t) in
  let l,t' = type_decomp res in
  let status,s =
   List.fold_right
    (fun x (status,res) ->
      let status,y = type2sign status x in
       status,y::res)
    l (status,[]) in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits uri(*CSC: (ConstRef uri)*) s in
  (* Decomposing the top level lambdas of [body].
     If there isn't enough, it's ok, as long as remaining args
     aren't to be pruned (and initial lambdas aren't to be all
     removed if the target language is strict). In other situations,
     eta-expansions create artificially enough lams (but that may
     break user's clever let-ins and partial applications). *)
  let rels, c =
    let n = List.length s
    and m = nb_lam body in
    if n <= m then decompose_lam_n n body
    else
      let s,s' = list_split_at m s in
      if List.for_all ((=) Keep) s' && sign_kind s <> UnsafeLogicalSig
      then decompose_lam_n m body
      else decomp_lams_eta_n n m status [] body typ
  in
  (* Should we do one eta-expansion to avoid non-generalizable '_a ? *)
  let rels, c =
    let n = List.length rels in
    let s,s' = list_split_at n s in
    let k = sign_kind s in
    let empty_s = (k = EmptySig || k = SafeLogicalSig) in
    if empty_s && not (gentypvar_ok c) && s' <> [] && type_maxvar t <> 0
    then decomp_lams_eta_n (n+1) n status [] body typ
    else rels,c
  in
  let n = List.length rels in
  let s = list_firstn n s in
  let l,l' = list_split_at n l in
  let t' = type_recomp (l',t') in
  (* The initial ML environment. *)
  let mle = List.fold_left Mlenv.push_std_type Mlenv.empty l in
  (* The lambdas names. *)
  let ids = List.map (fun (n,_) -> Id (id_of_name n)) rels in
  (* The according Coq environment. *)
  let context = rels in
  (* The real extraction: *)
  let status,e = extract_term status context mle t' c [] in
  (* Expunging term and type from dummy lambdas. *)
  let trm = term_expunge s (ids,e) in
  let trm = handle_exn uri n (fun i -> fst (List.nth rels (i-1))) trm in
  let status,res = type_expunge_from_sign status s t in
  status,trm,res

let extract_constant_spec status r bo typ =
  match flag_of_type status [] typ with
    | (Logic, TypeScheme) ->
       status,Stype (r, [], Some (Tdummy Ktype))
    | (Logic, Default) -> status,Sval (r, Tdummy Kother)
    | (Info, TypeScheme) ->
        let s,vl = type_sign_vl status [] typ in
        (match bo with
          | None -> status,Stype (r, vl, None)
          | Some body ->
              let db = db_from_sign s in
              let status,t =
               extract_type_scheme status [] db body (List.length s) in
              status,Stype (r, vl, Some t))
    | (Info, Default) ->
        let status,(_,t) = record_constant_type status r (Some typ) in
        let status,res = type_expunge status t in
        status,Sval (r,res)


let extract_fixpoint_common uri height fix_or_cofix ifl =
  let recparamnoi,ti,ci =
   List.fold_right
    (fun (_,_,recparamno,ty,bo) (recparamnos,tys,bos) ->
      recparamno::recparamnos,ty::tys,bo::bos) ifl ([],[],[]) in
  let recparamnoi = Array.of_list recparamnoi in
  let ti = Array.of_list ti in
  let ci = Array.of_list ci in
  let n = Array.length ti in
  let vkn =
   Array.init n
    (fun i ->
      if fix_or_cofix then
       NReference.reference_of_spec uri
        (NReference.Fix (i,recparamnoi.(i),height))
      else
       NReference.reference_of_spec uri (NReference.CoFix i)) in
  ti,ci,n,vkn

(*s Is a [ml_spec] logical ? *)
let logical_spec = function
  | Stype (_, [], Some (Tdummy _)) -> true
  | Sval (_,Tdummy _) -> true
  | Sind i -> array_for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

let extract_fixpoint status uri height fix_or_cofix is_projection ifl =
  let status =
   if is_projection then
    let _,_,recparamno,_,_ = List.nth ifl 0 in
    let fieldspec = NReference.Fix (0,recparamno,height) in
    let ref = NReference.reference_of_spec uri fieldspec in
     confirm_projection status ref
   else
    status in
  let ti,ci,_,vkn= extract_fixpoint_common uri height fix_or_cofix ifl in
  current_fixpoints := Some uri;
  let status,res = array_mapi_status status
   (fun status i _ ->
     let _,head = split_all_prods status ~subst:[] [] ti.(i) in
     match head with
        NCic.Sort s when classify_sort s = InProp -> status,`None
      | NCic.Sort _ ->
         let n = type_scheme_nb_args status [] ti.(i) in
         let ids = iterate (fun l -> anonymous_name::l) n [] in
         status,`Type (Dtype (vkn.(i), ids, Tunknown))
      | _ ->
        if sort_of status [] ti.(i) <> InProp then
         let status,e,t = extract_std_constant status vkn.(i) ci.(i) ti.(i) in
          status,`Some (e,t)
        else
          status,`None
   ) ti in
  let axioms,terms,types =
   Array.fold_right
    (fun x ((axioms,terms,types) as res) ->
      match x with
         `None -> res
       | `Some (t,ty) -> axioms,t::terms,ty::types
       | `Type decl -> decl::axioms,terms,types
    ) res ([],[],[]) in
  current_fixpoints := None;
  status,axioms @ [Dfix (vkn, Array.of_list terms, Array.of_list types)]

let extract_fixpoint_spec status uri height fix_or_cofix ifl =
  let ti,_,_,vkn= extract_fixpoint_common uri height fix_or_cofix ifl in
  let status,specs =
   array_mapi_status status
    (fun status i vkn ->
      if sort_of status [] ti.(i) <> InProp then begin
       let status,spec = extract_constant_spec status vkn None ti.(i) in
       status, if logical_spec spec then None else Some spec
      end
     else status,None
    ) vkn in
  status,HExtlib.filter_map (fun x -> x) (Array.to_list specs)

let extract_constant status r bo typ =
  match bo with
    | None -> (* A logical axiom is risky, an informative one is fatal. *)
        (match flag_of_type status [] typ with
           | (Info,TypeScheme) ->
               if true (*CSC: not (is_custom r)*) then () (*CSC: only for warnings add_info_axiom r*);
               let n = type_scheme_nb_args status [] typ in
               let ids = iterate (fun l -> anonymous_name::l) n [] in
               status,Dtype (r, ids, Taxiom)
           | (Info,Default) ->
               if true (*CSC: not (is_custom r)*) then () (*CSC: only for warnings add_info_axiom r*);
               let status,(_,t) = record_constant_type status r (Some typ) in
               let status,res = type_expunge status t in
               status, Dterm (r, MLaxiom, res)
           | (Logic,TypeScheme) ->
               (*CSC: only for warnings add_log_axiom r;*)
               status,Dtype (r, [], Tdummy Ktype)
           | (Logic,Default) ->
               (*CSC: only for warnings add_log_axiom r;*)
               status,Dterm (r, MLdummy, Tdummy Kother))
    | Some body ->
        (match flag_of_type status [] typ with
           | (Logic, Default) ->
              status,Dterm (r, MLdummy, Tdummy Kother)
           | (Logic, TypeScheme) ->
              status,Dtype (r, [], Tdummy Ktype)
           | (Info, Default) ->
               let status,e,t = extract_std_constant status r body typ in
               status,Dterm (r,e,t)
           | (Info, TypeScheme) ->
               let s,vl = type_sign_vl status [] typ in
               let db = db_from_sign s in
               let status,t =
                extract_type_scheme status [] db body (List.length s)
               in status,Dtype (r, vl, t))

let extract_inductive status uri inductive ind_pragma leftno types =
  let status,ind = extract_ind0 status uri inductive ind_pragma leftno types in
  (*CSC: add_recursors status kn;*)
  let f status _i _j l =
    let implicits = [] (*CSC:implicits_of_global (ConstructRef ((kn,i),j+1))*) in
    let rec filter status i = function
      | [] -> status,[]
      | t::l ->
          let status,l' = filter status (succ i) l in
          let status,res = expand status t in
          if isDummy res || List.mem i implicits then status,l'
          else status,t::l'
    in filter status 1 l
  in
  let status,packets =
    array_fold_right_i
     (fun i p (status,res) ->
       let status,types = 
        array_fold_right_i
        (fun j x (status,res) ->
          let status,y = f status i j x in
           status,y::res
        ) p.ip_types (status,[])
       in
        status, { p with ip_types = Array.of_list types }::res
     ) ind.ind_packets (status,[])
  in status,{ ind with ind_packets = Array.of_list packets }

(*s Is a [ml_decl] logical ? *)

let logical_decl = function
  | Dterm (_,MLdummy,Tdummy _) -> true
  | Dtype (_,[],Tdummy _) -> true
  | Dfix (_,av,tv) ->
      (array_for_all ((=) MLdummy) av) &&
      (array_for_all isDummy tv)
  | Dind i -> array_for_all (fun ip -> ip.ip_logical) i.ind_packets
  | _ -> false

let extract_impl status (uri,height,metasenv,subst,obj_kind) =
 assert (metasenv=[]);
 assert (subst=[]);
 let status,decl =
  match obj_kind with
     NCic.Constant (_,_,bo,typ,_) ->
      let r =
       let spec =
        match bo with
           None -> NReference.Decl
         | Some _ -> NReference.Def height
       in NReference.reference_of_spec uri spec
      in
      let status,res = extract_constant status r bo typ in
       status,[res]
   | NCic.Inductive (inductive,leftno,types,(_,ind_pragma)) ->
      let status,res =
       extract_inductive status uri inductive ind_pragma leftno types
      in
       status,[Dind res]
   | NCic.Fixpoint (fix_or_cofix,ifl,(_,_,def_pragma)) ->
      extract_fixpoint status uri height fix_or_cofix
       (def_pragma = `Projection) ifl
 in
  status, List.filter (fun decl -> not (logical_decl decl)) decl
;;

let extract_spec status (uri,height,metasenv,subst,obj_kind) =
 assert (metasenv=[]);
 assert (subst=[]);
 match obj_kind with
    NCic.Constant (_,_,bo,typ,_) ->
     let r =
      let spec =
       match bo with
          None -> NReference.Decl
        | Some _ -> NReference.Def height
      in NReference.reference_of_spec uri spec
     in
     let status,spec = extract_constant_spec status r bo typ in
     status,if logical_spec spec then [] else [spec]
  | NCic.Inductive (inductive,leftno,types,(_,ind_pragma)) ->
     let status,res =
      extract_inductive status uri inductive ind_pragma leftno types in
     let spec = Sind res in
     status,if logical_spec spec then [] else [spec]
  | NCic.Fixpoint (fix_or_cofix,ifl,_) ->
     extract_fixpoint_spec status uri height fix_or_cofix ifl

let extract status obj =
 let status,res = extract_impl status obj in
 let status,resl = extract_spec status obj in
  status,res,resl
