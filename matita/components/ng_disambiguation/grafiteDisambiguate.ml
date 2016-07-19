(*
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

(* $Id: grafiteDisambiguate.ml 13145 2016-03-13 17:30:14Z fguidi $ *)

type db = {
  aliases: GrafiteAst.alias_spec DisambiguateTypes.Environment.t;
  multi_aliases: GrafiteAst.alias_spec list DisambiguateTypes.Environment.t;
  new_aliases: (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) list
}

let initial_status = {
  aliases = DisambiguateTypes.Environment.empty;
  multi_aliases = DisambiguateTypes.Environment.empty;
  new_aliases = []
}

class type g_status =
  object
   inherit Interpretations.g_status
   method disambiguate_db: db
  end

class virtual status =
 object (self)
  inherit Interpretations.status
  val disambiguate_db = initial_status
  method disambiguate_db = disambiguate_db
  method set_disambiguate_db v = {< disambiguate_db = v >}
  method set_disambiguate_status
   : 'status. #g_status as 'status -> 'self
      = fun o -> ((self#set_interp_status o)#set_disambiguate_db o#disambiguate_db)
 end

let eval_with_new_aliases status f =
 let status =
  status#set_disambiguate_db { status#disambiguate_db with new_aliases = [] } in
 let res = f status in
 let new_aliases = status#disambiguate_db.new_aliases in
  new_aliases,res
;;

let dump_aliases out msg status =
   out (if msg = "" then "aliases dump:" else msg ^ ": aliases dump:");
   DisambiguateTypes.Environment.iter (fun _ x -> out (GrafiteAstPp.pp_alias x))
    status#disambiguate_db.aliases
   
let set_proof_aliases status ~implicit_aliases mode new_aliases =
 if mode = GrafiteAst.WithoutPreferences then
   status
 else
   let aliases =
    List.fold_left (fun acc (d,c) -> DisambiguateTypes.Environment.add d c acc)
     status#disambiguate_db.aliases new_aliases in
   let multi_aliases =
    List.fold_left (fun acc (d,c) -> 
      DisambiguateTypes.Environment.cons GrafiteAst.description_of_alias 
         d c acc)
     status#disambiguate_db.multi_aliases new_aliases
   in
   let new_status =
    {multi_aliases = multi_aliases ;
     aliases = aliases;
     new_aliases =
      (if implicit_aliases then new_aliases else []) @
        status#disambiguate_db.new_aliases}
   in
    status#set_disambiguate_db new_status

exception BaseUriNotSetYet

let singleton msg = function
  | [x], _ -> x
  | l, _   ->
      let debug = 
         Printf.sprintf "GrafiteDisambiguate.singleton (%s): %u interpretations"
         msg (List.length l)
      in
      prerr_endline debug; assert false

let __Implicit = "__Implicit__"
let __Closed_Implicit = "__Closed_Implicit__"

let ncic_mk_choice status = function
  | GrafiteAst.Symbol_alias (name, _, dsc) ->
     if name = __Implicit then
       dsc, `Sym_interp (fun _ -> NCic.Implicit `Term)
     else if name = __Closed_Implicit then 
       dsc, `Sym_interp (fun _ -> NCic.Implicit `Closed)
     else
       DisambiguateChoices.lookup_symbol_by_dsc status
        ~mk_implicit:(function 
           | true -> NCic.Implicit `Closed
           | false -> NCic.Implicit `Term)
        ~mk_appl:(function 
           (NCic.Appl l)::tl -> NCic.Appl (l@tl) | l -> NCic.Appl l)
        ~term_of_nref:(fun nref -> NCic.Const nref)
       name dsc
  | GrafiteAst.Number_alias (_, dsc) -> 
     let desc,f = DisambiguateChoices.nlookup_num_by_dsc dsc in
      desc, `Num_interp
       (fun num -> match f with `Num_interp f -> f num | _ -> assert false)
  | GrafiteAst.Ident_alias (name, uri) -> 
     uri, `Sym_interp 
      (fun l->assert(l = []);
        let nref = NReference.reference_of_string uri in
         NCic.Const nref)
;;


let mk_implicit b =
  match b with
  | false -> 
      GrafiteAst.Symbol_alias (__Implicit,-1,"Fake Implicit")
  | true -> 
      GrafiteAst.Symbol_alias (__Closed_Implicit,-1,"Fake Closed Implicit")
;;

let nlookup_in_library 
  interactive_user_uri_choice input_or_locate_uri item 
=
  match item with
  | DisambiguateTypes.Id id -> 
     (try
       let references = NCicLibrary.resolve id in
        List.map
         (fun u -> GrafiteAst.Ident_alias (id,NReference.string_of_reference u)
         ) references
      with
       NCicEnvironment.ObjectNotFound _ -> [])
  | _ -> []
;;

let fix_instance item l =
 match item with
    DisambiguateTypes.Symbol (_,n) ->
     List.map
      (function
          GrafiteAst.Symbol_alias (s,_,d) -> GrafiteAst.Symbol_alias (s,n,d)
        | _ -> assert false
      ) l
  | DisambiguateTypes.Num n ->
     List.map
      (function
          GrafiteAst.Number_alias (_,d) -> GrafiteAst.Number_alias (n,d)
        | _ -> assert false
      ) l
  | DisambiguateTypes.Id _ -> l
;;


let disambiguate_nterm status expty context metasenv subst thing
=
  let diff, metasenv, subst, cic =
    singleton "first"
      (NCicDisambiguate.disambiguate_term
        status
        ~aliases:status#disambiguate_db.aliases
        ~expty 
        ~universe:(Some status#disambiguate_db.multi_aliases)
        ~lookup_in_library:nlookup_in_library
        ~mk_choice:(ncic_mk_choice status)
        ~mk_implicit ~fix_instance
        ~description_of_alias:GrafiteAst.description_of_alias
        ~context ~metasenv ~subst thing)
  in
  let status =
   set_proof_aliases status ~implicit_aliases:true GrafiteAst.WithPreferences
    diff
  in
   metasenv, subst, status, cic
;;


type pattern = 
  NotationPt.term Disambiguate.disambiguator_input option * 
  (string * NCic.term) list * NCic.term option

let disambiguate_npattern status (text, prefix_len, (wanted, hyp_paths, goal_path)) =
  let interp path = NCicDisambiguate.disambiguate_path status path in
  let goal_path = HExtlib.map_option interp goal_path in
  let hyp_paths = List.map (fun (name, path) -> name, interp path) hyp_paths in
  let wanted = HExtlib.map_option (fun x -> text,prefix_len,x) wanted in
   (wanted, hyp_paths, goal_path)
;;

let disambiguate_reduction_kind text prefix_len = function
  | `Unfold (Some t) -> assert false (* MATITA 1.0 *)
  | `Normalize
  | `Simpl
  | `Unfold None
  | `Whd as kind -> kind
;;

let disambiguate_auto_params 
  disambiguate_term metasenv context (oterms, params) 
=
  match oterms with 
    | None -> metasenv, (None, params)
    | Some terms ->
	let metasenv, terms = 
	  List.fold_right 
	    (fun t (metasenv, terms) ->
               let metasenv,t = disambiguate_term context metasenv t in
		 metasenv,t::terms) terms (metasenv, [])
	in
	  metasenv, (Some terms, params)
;;

let disambiguate_just disambiguate_term context metasenv =
 function
    `Term t ->
      let metasenv,t = disambiguate_term context metasenv t in
       metasenv, `Term t
  | `Auto params ->
      let metasenv,params = disambiguate_auto_params disambiguate_term metasenv
       context params
      in
       metasenv, `Auto params
;;
      
let disambiguate_nobj status ?baseuri (text,prefix_len,obj) =
  let uri =
   let baseuri = 
     match baseuri with Some x -> x | None -> raise BaseUriNotSetYet
   in
   let name = 
     match obj with
     | NotationPt.Inductive (_,(name,_,_,_)::_,_)
     | NotationPt.Record (_,name,_,_,_) -> name ^ ".ind"
     | NotationPt.Theorem (name,_,_,_) -> name ^ ".con"
     | NotationPt.LetRec (_,(_,(NotationPt.Ident (name, None),_),_,_)::_,_) -> name ^ ".con"
     | NotationPt.LetRec _
     | NotationPt.Inductive _ -> assert false
   in
     NUri.uri_of_string (baseuri ^ "/" ^ name)
  in
  let diff, _, _, cic =
   singleton "third"
    (NCicDisambiguate.disambiguate_obj
      status
      ~lookup_in_library:nlookup_in_library
      ~description_of_alias:GrafiteAst.description_of_alias
      ~mk_choice:(ncic_mk_choice status)
      ~mk_implicit ~fix_instance ~uri
      ~aliases:status#disambiguate_db.aliases
      ~universe:(Some status#disambiguate_db.multi_aliases) 
      (text,prefix_len,obj)) in
  let status =
   set_proof_aliases status ~implicit_aliases:true GrafiteAst.WithPreferences
    diff
  in
   status, cic
;;

let disambiguate_cic_appl_pattern status args =
 let rec disambiguate =
  function
    NotationPt.ApplPattern l ->
     NotationPt.ApplPattern (List.map disambiguate l)
  | NotationPt.VarPattern id
     when not
      (List.exists
       (function (NotationPt.IdentArg (_,id')) -> id'=id) args)
     ->
      let item = DisambiguateTypes.Id id in
       begin
        try
         match
          DisambiguateTypes.Environment.find item
           status#disambiguate_db.aliases
         with
            GrafiteAst.Ident_alias (_, uri) ->
             NotationPt.NRefPattern (NReference.reference_of_string uri)
          | _ -> assert false
        with Not_found -> 
         prerr_endline
          ("LexiconEngine.eval_command: domain item not found: " ^ 
          (DisambiguateTypes.string_of_domain_item item));
         dump_aliases prerr_endline "" status;
         raise 
          (Failure
           ((DisambiguateTypes.string_of_domain_item item) ^ " not found"))
             end
  | p -> p
 in
  disambiguate
;;

let aliases_for_objs status refs =
 List.concat
  (List.map
    (fun nref ->
      let references = NCicLibrary.aliases_of nref in
       List.map
        (fun u ->
          let name = NCicPp.r2s status true u in
           DisambiguateTypes.Id name,
            GrafiteAst.Ident_alias (name,NReference.string_of_reference u)
        ) references) refs)
