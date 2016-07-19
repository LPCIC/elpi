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

(* $Id: disambiguate.ml 13145 2016-03-13 17:30:14Z fguidi $ *)

open Printf

open DisambiguateTypes

module Ast = NotationPt

(* the integer is an offset to be added to each location *)
exception Ambiguous_input
(* the integer is an offset to be added to each location *)
exception NoWellTypedInterpretation of
 int *
 ((Stdpp.location list * string * string) list *
  (DisambiguateTypes.domain_item * string) list *
  (Stdpp.location * string) Lazy.t * bool) list
exception PathNotWellFormed

  (** raised when an environment is not enough informative to decide *)
exception Try_again of string Lazy.t

type ('alias,'term) aliases =
 bool * 'term DisambiguateTypes.codomain_item DisambiguateTypes.Environment.t
type 'a disambiguator_input = string * int * 'a

type domain = domain_tree list
and domain_tree = Node of Stdpp.location list * domain_item * domain

let mono_uris_callback ~selection_mode ?ok
          ?(enable_button_for_non_vars = true) ~title ~msg ~id =
 if Helm_registry.get_opt_default Helm_registry.get_bool ~default:true
      "matita.auto_disambiguation"
 then
  function l -> l
 else
  raise Ambiguous_input

let mono_interp_callback _ _ _ = raise Ambiguous_input

let _choose_uris_callback = ref mono_uris_callback
let _choose_interp_callback = ref mono_interp_callback
let set_choose_uris_callback f = _choose_uris_callback := f
let set_choose_interp_callback f = _choose_interp_callback := f

let interactive_user_uri_choice = !_choose_uris_callback
let interactive_interpretation_choice interp = !_choose_interp_callback interp
let input_or_locate_uri ~(title:string) ?id () = None
  (* Zack: I try to avoid using this callback. I therefore assume that
  * the presence of an identifier that can't be resolved via "locate"
  * query is a syntax error *)
  

let rec string_of_domain =
 function
    [] -> ""
  | Node (_,domain_item,l)::tl ->
     DisambiguateTypes.string_of_domain_item domain_item ^
      " [ " ^ string_of_domain l ^ " ] " ^ string_of_domain tl

let rec filter_map_domain f =
 function
    [] -> []
  | Node (locs,domain_item,l)::tl ->
     match f locs domain_item with
        None -> filter_map_domain f l @ filter_map_domain f tl
      | Some res -> res :: filter_map_domain f l @ filter_map_domain f tl

let rec map_domain f =
 function
    [] -> []
  | Node (locs,domain_item,l)::tl ->
     f locs domain_item :: map_domain f l @ map_domain f tl

let uniq_domain dom =
 let rec aux seen =
  function
     [] -> seen,[]
   | Node (locs,domain_item,l)::tl ->
      if List.mem domain_item seen then
       let seen,l = aux seen l in
       let seen,tl = aux seen tl in
        seen, l @ tl
      else
       let seen,l = aux (domain_item::seen) l in
       let seen,tl = aux seen tl in
        seen, Node (locs,domain_item,l)::tl
 in
  snd (aux [] dom)

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

(*
  (** print benchmark information *)
let benchmark = true
let max_refinements = ref 0       (* benchmarking is not thread safe *)
let actual_refinements = ref 0
let domain_size = ref 0
let choices_avg = ref 0.
*)

let descr_of_domain_item = function
 | Id s -> s
 | Symbol (s, _) -> s
 | Num i -> string_of_int i

type ('term,'metasenv,'subst,'graph) test_result =
  | Ok of 'term * 'metasenv * 'subst * 'graph
  | Ko of (Stdpp.location * string) Lazy.t
  | Uncertain of (Stdpp.location * string) Lazy.t

let resolve ~env ~mk_choice (item: domain_item) arg =
  try
   match snd (mk_choice (Environment.find item env)), arg with
      `Num_interp f, `Num_arg n -> f n
    | `Sym_interp f, `Args l -> f l
    | `Sym_interp f, `Num_arg n -> (* Implicit number! *) f []
    | _,_ -> assert false
  with Not_found -> 
    failwith ("Domain item not found: " ^ 
      (DisambiguateTypes.string_of_domain_item item))

  (* TODO move it to Cic *)
let find_in_context name context =
  let rec aux acc = function
    | [] -> raise Not_found
    | Some hd :: tl when hd = name -> acc
    | _ :: tl ->  aux (acc + 1) tl
  in
  aux 1 context

let string_of_name =
 function
  | Ast.Ident (n, None) -> Some n
  | _ -> assert false
;;

let rec domain_of_term ?(loc = HExtlib.dummy_floc) ~context = function
  | Ast.AttributedTerm (`Loc loc, term) ->
     domain_of_term ~loc ~context term
  | Ast.AttributedTerm (_, term) ->
      domain_of_term ~loc ~context term
  | Ast.Symbol (symbol, instance) ->
      [ Node ([loc], Symbol (symbol, instance), []) ]
      (* to be kept in sync with Ast.Appl (Ast.Symbol ...) *)
  | Ast.Appl (Ast.Symbol (symbol, instance) as hd :: args)
  | Ast.Appl (Ast.AttributedTerm (_,Ast.Symbol (symbol, instance)) as hd :: args)
     ->
      let args_dom =
        List.fold_right
          (fun term acc -> domain_of_term ~loc ~context term @ acc)
          args [] in
      let loc =
       match hd with
          Ast.AttributedTerm (`Loc loc,_)  -> loc
        | _ -> loc
      in
       [ Node ([loc], Symbol (symbol, instance), args_dom) ]
  | Ast.Appl (Ast.Ident (name, subst) as hd :: args)
  | Ast.Appl (Ast.AttributedTerm (_,Ast.Ident (name, subst)) as hd :: args) ->
      let args_dom =
        List.fold_right
          (fun term acc -> domain_of_term ~loc ~context term @ acc)
          args [] in
      let loc =
       match hd with
          Ast.AttributedTerm (`Loc loc,_)  -> loc
        | _ -> loc
      in
      (try
        (* the next line can raise Not_found *)
        ignore(find_in_context name context);
        if subst <> None then
          Ast.fail loc "Explicit substitutions not allowed here"
        else
          args_dom
      with Not_found ->
        (match subst with
        | None -> [ Node ([loc], Id name, args_dom) ]
        | Some subst ->
            let terms =
              List.fold_left
                (fun dom (_, term) ->
                  let dom' = domain_of_term ~loc ~context term in
                  dom @ dom')
                [] subst in
            [ Node ([loc], Id name, terms @ args_dom) ]))
  | Ast.Appl terms ->
      List.fold_right
        (fun term acc -> domain_of_term ~loc ~context term @ acc)
        terms []
  | Ast.Binder (kind, (var, typ), body) ->
      let type_dom = domain_of_term_option ~loc ~context typ in
      let body_dom =
        domain_of_term ~loc
          ~context:(string_of_name var :: context) body in
      (match kind with
      | `Exists -> [ Node ([loc], Symbol ("exists", 0), (type_dom @ body_dom)) ]
      | _ -> type_dom @ body_dom)
  | Ast.Case (term, indty_ident, outtype, branches) ->
      let term_dom = domain_of_term ~loc ~context term in
      let outtype_dom = domain_of_term_option ~loc ~context outtype in
      let rec get_first_constructor = function
        | [] -> []
        | (Ast.Pattern (head, _, _), _) :: _ -> [ Node ([loc], Id head, []) ]
        | _ :: tl -> get_first_constructor tl in
      let do_branch =
       function
          Ast.Pattern (head, _, args), term ->
           let (term_context, args_domain) =
             List.fold_left
               (fun (cont, dom) (name, typ) ->
                 (string_of_name name :: cont,
                  (match typ with
                  | None -> dom
                  | Some typ -> dom @ domain_of_term ~loc ~context:cont typ)))
               (context, []) args
           in
            domain_of_term ~loc ~context:term_context term @ args_domain
        | Ast.Wildcard, term ->
            domain_of_term ~loc ~context term
      in
      let branches_dom =
        List.fold_left (fun dom branch -> dom @ do_branch branch) [] branches in
      (match indty_ident with
       | None -> get_first_constructor branches
       | Some (ident, _) -> [ Node ([loc], Id ident, []) ])
      @ term_dom @ outtype_dom @ branches_dom
  | Ast.Cast (term, ty) ->
      let term_dom = domain_of_term ~loc ~context term in
      let ty_dom = domain_of_term ~loc ~context ty in
      term_dom @ ty_dom
  | Ast.LetIn ((var, typ), body, where) ->
      let body_dom = domain_of_term ~loc ~context body in
      let type_dom = domain_of_term_option ~loc ~context typ in
      let where_dom =
        domain_of_term ~loc ~context:(string_of_name var :: context) where in
      body_dom @ type_dom @ where_dom
  | Ast.Ident (name, subst) ->
      (try
        (* the next line can raise Not_found *)
        ignore(find_in_context name context);
        if subst <> None then
          Ast.fail loc "Explicit substitutions not allowed here"
        else
          []
      with Not_found ->
        (match subst with
        | None -> [ Node ([loc], Id name, []) ]
        | Some subst ->
            let terms =
              List.fold_left
                (fun dom (_, term) ->
                  let dom' = domain_of_term ~loc ~context term in
                  dom @ dom')
                [] subst in
            [ Node ([loc], Id name, terms) ]))
  | Ast.Uri _ -> []
  | Ast.NRef _ -> []
  | Ast.NCic _ -> []
  | Ast.Implicit _ -> []
  | Ast.Num (num, i) -> [ Node ([loc], Num i, []) ]
  | Ast.Meta (index, local_context) ->
      List.fold_left
       (fun dom term -> dom @ domain_of_term_option ~loc ~context term)
       [] local_context
  | Ast.Sort _ -> []
  | Ast.UserInput
  | Ast.Literal _
  | Ast.Layout _
  | Ast.Magic _
  | Ast.Variable _ -> assert false

and domain_of_term_option ~loc ~context = function
  | None -> []
  | Some t -> domain_of_term ~loc ~context t

let domain_of_term ~context term = 
 uniq_domain (domain_of_term ~context term)

let domain_of_term_option ~context = function
   | None      -> []
   | Some term -> domain_of_term ~context term

let domain_of_obj ~context ast =
 assert (context = []);
  match ast with
   | Ast.Theorem (_,ty,bo,_) ->
      domain_of_term [] ty
      @ (match bo with
          None -> []
        | Some bo -> domain_of_term [] bo)
   | Ast.Inductive (params,tyl,_) ->
      let context, dom = 
       List.fold_left
        (fun (context, dom) (var, ty) ->
          let context' = string_of_name var :: context in
          match ty with
             None -> context', dom
           | Some ty -> context', dom @ domain_of_term context ty
        ) ([], []) params in
      let context_w_types =
        List.rev_map (fun (var, _, _, _) -> Some var) tyl @ context in
      dom
      @ List.flatten (
         List.map
          (fun (_,_,ty,cl) ->
            domain_of_term context ty
            @ List.flatten (
               List.map
                (fun (_,ty) -> domain_of_term context_w_types ty) cl))
                tyl)
   | Ast.Record (params,var,ty,fields,_) ->
      let context, dom = 
       List.fold_left
        (fun (context, dom) (var, ty) ->
          let context' = string_of_name var :: context in
          match ty with
             None -> context', dom
           | Some ty -> context', dom @ domain_of_term context ty
        ) ([], []) params in
      let context_w_types = Some var :: context in
      dom
      @ domain_of_term context ty
      @ snd
         (List.fold_left
          (fun (context,res) (name,ty,_,_) ->
            Some name::context, res @ domain_of_term context ty
          ) (context_w_types,[]) fields)
   | Ast.LetRec (kind, defs, _) ->
       let add_defs context =
         List.fold_left
           (fun acc (_, (var, _), _, _) -> string_of_name var :: acc
           ) context defs in
       let defs_dom =
         List.fold_left
           (fun dom (params, (_, typ), body, _) ->
             let context' =
              add_defs
               (List.fold_left
                 (fun acc (var,_) -> string_of_name var :: acc)
                 context params)
             in
             List.rev
              (snd
                (List.fold_left
                 (fun (context,res) (var,ty) ->
                   string_of_name var :: context,
                   domain_of_term_option ~context ty @ res)
                 (add_defs context,[]) params))
             @ dom
             @ domain_of_term_option ~context:context' typ
             @ domain_of_term ~context:context' body
           ) [] defs
      in
      defs_dom

let domain_of_obj ~context obj = 
 uniq_domain (domain_of_obj ~context obj)

  (* dom1 \ dom2 *)
let domain_diff dom1 dom2 =
(* let domain_diff = Domain.diff *)
  let is_in_dom2 elt =
    List.exists
     (function
       | Symbol (symb, 0) ->
          (match elt with
              Symbol (symb',_) when symb = symb' -> true
            | _ -> false)
       | Num i ->
          (match elt with
              Num _ -> true
            | _ -> false)
       | item -> elt = item
     ) dom2
  in
   let rec aux =
    function
       [] -> []
     | Node (_,elt,l)::tl when is_in_dom2 elt -> aux (l @ tl)
     | Node (loc,elt,l)::tl -> Node (loc,elt,aux l)::(aux tl)
   in
    aux dom1

let refine_profiler = HExtlib.profile "disambiguate_thing.refine_thing"

let disambiguate_thing 
  ~context ~metasenv ~subst ~use_coercions
  ~string_context_of_context
  ~initial_ugraph:base_univ ~expty
  ~mk_implicit ~description_of_alias ~fix_instance
  ~aliases ~universe ~lookup_in_library 
  ~uri ~pp_thing ~domain_of_thing ~interpretate_thing ~refine_thing 
  ~mk_localization_tbl
  (thing_txt,thing_txt_prefix_len,thing)
=
  debug_print (lazy "DISAMBIGUATE INPUT");
  debug_print (lazy ("TERM IS: " ^ (pp_thing thing)));
  let thing_dom =
    domain_of_thing ~context:(string_context_of_context context) thing in
  debug_print
   (lazy (sprintf "DISAMBIGUATION DOMAIN: %s"(string_of_domain thing_dom)));
   let current_dom =
     Environment.fold (fun item _ dom -> item :: dom) aliases [] in
   let todo_dom = domain_diff thing_dom current_dom in
   debug_print
    (lazy (sprintf "DISAMBIGUATION DOMAIN AFTER DIFF: %s"(string_of_domain todo_dom)));
   (* (2) lookup function for any item (Id/Symbol/Num) *)
   let lookup_choices =
     fun item ->
      match universe with
      | None -> 
          lookup_in_library 
            interactive_user_uri_choice 
            input_or_locate_uri item
      | Some e ->
          (try
            fix_instance item (Environment.find item e)
          with Not_found -> [])
   in

   (* items with 1 choice are interpreted ASAP *)
   let aliases, todo_dom = 
     let rec aux (aliases,acc) = function 
       | [] -> aliases, acc
       | (Node (locs, item,extra) as node) :: tl -> 
           let choices = lookup_choices item in
           if List.length choices = 0 then
            (* Quick failure *)
            raise (NoWellTypedInterpretation (0,[[],[],(lazy (List.hd locs, "No choices for " ^ string_of_domain_item item)),true]))
           else if List.length choices <> 1 then
            let aliases,extra = aux (aliases,[]) extra in
             aux (aliases, acc@[Node (locs,item,extra)]) tl
           else
           let tl = tl @ extra in
           if Environment.mem item aliases then aux (aliases, acc) tl
           else aux (Environment.add item (List.hd choices) aliases, acc) tl
     in
       aux (aliases,[]) todo_dom
   in
   debug_print
    (lazy(sprintf "TODO DOM: %s"(string_of_domain todo_dom)));

(*
      (* <benchmark> *)
      let _ =
        if benchmark then begin
          let per_item_choices =
            List.map
              (fun dom_item ->
                try
                  let len = List.length (lookup_choices dom_item) in
                  debug_print (lazy (sprintf "BENCHMARK %s: %d"
                    (string_of_domain_item dom_item) len));
                  len
                with No_choices _ -> 0)
              thing_dom
          in
          max_refinements := List.fold_left ( * ) 1 per_item_choices;
          actual_refinements := 0;
          domain_size := List.length thing_dom;
          choices_avg :=
            (float_of_int !max_refinements) ** (1. /. float_of_int !domain_size)
        end
      in
      (* </benchmark> *)
*)

   (* (3) test an interpretation filling with meta uninterpreted identifiers
    *)
   let test_env aliases todo_dom ugraph = 
     try
      let rec aux env = function
       | [] -> env
       | Node (_, item, l) :: tl ->
           let env =
             Environment.add item
              (mk_implicit
                (match item with | Id _ | Num _ -> true | Symbol _ -> false))
              env in
           aux (aux env l) tl in
      let filled_env = aux aliases todo_dom in
      let localization_tbl = mk_localization_tbl 503 in
       let cic_thing =
         interpretate_thing ~context ~env:filled_env
          ~uri ~is_path:false thing ~localization_tbl
       in
let foo () =
        refine_thing metasenv subst context uri
         ~use_coercions cic_thing expty ugraph ~localization_tbl
in refine_profiler.HExtlib.profile foo ()
     with
     | Try_again msg -> Uncertain (lazy (Stdpp.dummy_loc,Lazy.force msg))
     | Invalid_choice loc_msg -> Ko loc_msg
   in
   (* (4) build all possible interpretations *)
   let (@@) (l1,l2,l3) (l1',l2',l3') = l1@l1', l2@l2', l3@l3' in
   (* aux returns triples Ok/Uncertain/Ko *)
   (* rem_dom is the concatenation of all the remainin domains *)
   let rec aux aliases diff lookup_in_todo_dom todo_dom rem_dom =
     debug_print (lazy ("ZZZ: " ^ string_of_domain todo_dom));
     match todo_dom with
     | [] ->
         assert (lookup_in_todo_dom = None);
         (match test_env aliases rem_dom base_univ with
         | Ok (thing, metasenv,subst,new_univ) -> 
            [ aliases, diff, metasenv, subst, thing, new_univ ], [], []
         | Ko loc_msg -> [],[],[aliases,diff,loc_msg,true]
         | Uncertain loc_msg ->
            [],[aliases,diff,loc_msg],[])
     | Node (locs,item,inner_dom) :: remaining_dom ->
         debug_print (lazy (sprintf "CHOOSED ITEM: %s"
          (string_of_domain_item item)));
         let choices =
          match lookup_in_todo_dom with
             None -> lookup_choices item
           | Some choices -> choices in
         match choices with
            [] ->
             [], [],
              [aliases, diff, 
               (lazy (List.hd locs,
                 "No choices for " ^ string_of_domain_item item)),
               true]
          | _::_ ->
              let mark_not_significant failures =
                List.map
                 (fun (env, diff, loc_msg, _b) ->
                   env, diff, loc_msg, false)
                 failures in
              let classify_errors ((ok_l,uncertain_l,error_l) as outcome) =
               if ok_l <> [] || uncertain_l <> [] then
                ok_l,uncertain_l,mark_not_significant error_l
               else
                outcome in
            let rec filter = function 
             | [] -> [],[],[]
             | codomain_item :: tl ->
                 (*debug_print(lazy (sprintf "%s CHOSEN" (fst codomain_item)));*)
                let new_env = Environment.add item codomain_item aliases in
                let new_diff = (item,codomain_item)::diff in
                (match
                  test_env new_env 
                    (inner_dom@remaining_dom@rem_dom) base_univ
                 with
                | Ok (thing, metasenv,subst,new_univ) ->
(*prerr_endline ((sprintf "CHOOSED ITEM OK: %s" (string_of_domain_item item)));*)
                    let res = 
                      (match inner_dom with
                      | [] ->
                         [new_env,new_diff,metasenv,subst,thing,new_univ],
                         [], []
                      | _ ->
                         aux new_env new_diff None inner_dom
                          (remaining_dom@rem_dom) 
                      ) 
                    in
                     res @@ filter tl
                | Uncertain loc_msg ->
(*prerr_endline ((sprintf "CHOOSED ITEM UNCERTAIN: %s" (string_of_domain_item item) ^ snd (Lazy.force loc_msg)));*)
                    let res =
                      (match inner_dom with
                      | [] -> [],[new_env,new_diff,loc_msg],[]
                      | _ ->
                         aux new_env new_diff None inner_dom
                          (remaining_dom@rem_dom) 
                      )
                    in
                     res @@ filter tl
                | Ko loc_msg ->
(*prerr_endline ((sprintf "CHOOSED ITEM KO: %s" (string_of_domain_item item)));*)
                    let res = [],[],[new_env,new_diff,loc_msg,true] in
                     res @@ filter tl)
           in
            let ok_l,uncertain_l,error_l =
             classify_errors (filter choices)
            in
             let res_after_ok_l =
              List.fold_right
               (fun (env,diff,_,_,_,_) res ->
                 aux env diff None remaining_dom rem_dom @@ res
               ) ok_l ([],[],error_l)
            in
             List.fold_right
              (fun (env,diff,_) res ->
                aux env diff None remaining_dom rem_dom @@ res
              ) uncertain_l res_after_ok_l
  in
  let aux' aliases diff lookup_in_todo_dom todo_dom =
   if todo_dom = [] then
     aux aliases diff lookup_in_todo_dom todo_dom [] 
   else
     match test_env aliases todo_dom base_univ with
      | Ok _ 
      | Uncertain _ ->
         aux aliases diff lookup_in_todo_dom todo_dom [] 
      | Ko (loc_msg) -> [],[],[aliases,diff,loc_msg,true]
  in
    let res =
     match aux' aliases [] None todo_dom with
     | [],uncertain,errors ->
        let errors =
         List.map
          (fun (env,diff,loc_msg) -> (env,diff,loc_msg,true)
          ) uncertain @ errors
        in
        let errors =
         List.map
          (fun (env,diff,loc_msg,significant) ->
            let env' =
             filter_map_domain
               (fun locs domain_item ->
                 try
                  let description =
                   description_of_alias (Environment.find domain_item env)
                  in
                   Some (locs,descr_of_domain_item domain_item,description)
                 with
                  Not_found -> None)
               thing_dom
            in
            let diff= List.map (fun a,b -> a,description_of_alias b) diff in
             env',diff,loc_msg,significant
          ) errors
        in
         raise (NoWellTypedInterpretation (0,errors))
     | [_,diff,metasenv,subst,t,ugraph],_,_ ->
         debug_print (lazy "SINGLE INTERPRETATION");
         [diff,metasenv,subst,t,ugraph], false
     | l,_,_ ->
         debug_print 
           (lazy (sprintf "MANY INTERPRETATIONS (%d)" (List.length l)));
         let choices =
           List.map
             (fun (env, _, _, _, _, _) ->
               map_domain
                 (fun locs domain_item ->
                   let description =
                     description_of_alias (Environment.find domain_item env)
                   in
                   locs,descr_of_domain_item domain_item, description)
                 thing_dom)
             l
         in
         let choosed = 
           interactive_interpretation_choice 
             thing_txt thing_txt_prefix_len choices 
         in
         (List.map (fun n->let _,d,m,s,t,u= List.nth l n in d,m,s,t,u)
           choosed),
          true
    in
     res
