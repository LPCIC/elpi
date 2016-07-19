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

(* $Id: content2presMatcher.ml 11290 2011-05-30 11:02:26Z sacerdot $ *)

open Printf

module Ast = NotationPt
module Env = NotationEnv
module Pp = NotationPp
module Util = NotationUtil

let get_tag term0 =
  let subterms = ref [] in
  let map_term t =
    subterms := t :: !subterms ; 
    Ast.Implicit `JustOne
  in
  let rec aux t = 
    NotationUtil.visit_ast 
      ~map_xref_option:(fun _ -> None)
      ~map_case_indty:(fun _ -> None)
      ~map_case_outtype:(fun _ _ -> None)
      ~special_k map_term t
  and special_k = function
    | Ast.AttributedTerm (_, t) -> aux t
    | _ -> assert false
  in
  let term_mask = aux term0 in
  let tag = Hashtbl.hash term_mask in
  tag, List.rev !subterms

module Matcher21 =
struct
  module Pattern21 =
  struct
    type pattern_t = Ast.term
    type term_t = Ast.term
    let rec classify = function
      | Ast.AttributedTerm (_, t) -> classify t
      | Ast.Variable _ -> PatternMatcher.Variable
      | Ast.Magic _
      | Ast.Layout _
      | Ast.Literal _ -> assert false
      | _ -> PatternMatcher.Constructor
    let tag_of_pattern = get_tag
    let tag_of_term t = get_tag t

    (* Debugging only *)
    (*CSC: new NCicPp.status is the best I can do now *)
    let string_of_term = NotationPp.pp_term (new NCicPp.status)
    let string_of_pattern = NotationPp.pp_term (new NCicPp.status)
  end

  module M = PatternMatcher.Matcher (Pattern21)

  let extract_magic term =
    let magic_map = ref [] in
    let add_magic m =
      let name = Util.fresh_name () in
      magic_map := (name, m) :: !magic_map;
      Ast.Variable (Ast.TermVar (name,Ast.Level 0))
    in
    let rec aux = function
      | Ast.AttributedTerm (_, t) -> assert false
      | Ast.Literal _
      | Ast.Layout _ -> assert false
      | Ast.Variable v -> Ast.Variable v
      | Ast.Magic m -> add_magic m
      | t -> Util.visit_ast aux t
    in
    let term' = aux term in
    term', !magic_map

  let env_of_matched pl tl =
    try
      List.map2
        (fun p t ->
          match p, t with
          | Ast.Variable (Ast.TermVar (name,(Ast.Self l|Ast.Level l))), _ ->
              name, (Env.TermType l, Env.TermValue t)
          | Ast.Variable (Ast.NumVar name), (Ast.Num (s, _)) ->
              name, (Env.NumType, Env.NumValue s)
          | Ast.Variable (Ast.IdentVar name), (Ast.Ident (s, None)) ->
              name, (Env.StringType, Env.StringValue (Env.Ident s))
          | _ -> assert false (* activate the DEBUGGING CODE below *))
        pl tl
    with Invalid_argument _ -> assert false

  let rec compiler rows =
    let rows', magic_maps =
      List.split
        (List.map
          (fun (p, pid) ->
            let p', map = extract_magic p in
            (p', pid), (pid, map))
          rows)
    in
    let magichecker map =
      List.fold_left
        (fun f (name, m) ->
          let m_checker = compile_magic m in
          (fun env ctors ->
            match m_checker (Env.lookup_term env name) env ctors with
            | None -> None
            | Some (env, ctors) -> f env ctors))
        (fun env ctors -> Some (env, ctors))
        map
    in
    let magichooser candidates =
      List.fold_left
        (fun f (pid, pl, checker) ->
          (fun matched_terms constructors ->
            let env = env_of_matched pl matched_terms in
            match checker env constructors with
            | None -> f matched_terms constructors
            | Some (env, ctors') ->
		let magic_map =
		  try List.assoc pid magic_maps with Not_found -> assert false
		in
		let env' = Env.remove_names env (List.map fst magic_map) in
		Some (env', ctors', pid)))
        (fun _ _ -> None)
        (List.rev candidates)
    in
    let match_cb rows =
      let candidates =
        List.map
          (fun (pl, pid) ->
            let magic_map =
              try List.assoc pid magic_maps with Not_found -> assert false
            in
            pid, pl, magichecker magic_map)
          rows
      in
      magichooser candidates
    in
(* DEBUGGING CODE 
fun input ->
let (fst,_)::_ = rows in
prerr_endline ("RIGA: " ^ NotationPp.pp_term (new NCicPp.status) fst);
prerr_endline ("CONTRO: " ^ NotationPp.pp_term (new NCicPp.status) input);
*)
    M.compiler rows' match_cb (fun _ -> None)
(* DEBUGGING CODE 
input
*)

  and compile_magic = function
    | Ast.Fold (kind, p_base, names, p_rec) ->
        let p_rec_decls = Env.declarations_of_term p_rec in
	  (* LUCA: p_rec_decls should not contain "names" *)
        let acc_name = try List.hd names with Failure _ -> assert false in
	let compiled_base = compiler [p_base, 0]
	and compiled_rec = compiler [p_rec, 0] in
	  (fun term env ctors ->
	     let aux_base term =
	       match compiled_base term with
		 | None -> None
		 | Some (env', ctors', _) -> Some (env', ctors', [])
	     in
	     let rec aux term =
	       match compiled_rec term with
		 | None -> aux_base term
		 | Some (env', ctors', _) ->
		     begin
                       let acc = Env.lookup_term env' acc_name in
                       let env'' = Env.remove_name env' acc_name in
			 match aux acc with
			   | None -> aux_base term
			   | Some (base_env, ctors', rec_envl) -> 
                               let ctors'' = ctors' @ ctors in
			       Some (base_env, ctors'',env'' :: rec_envl)
                     end
	     in
               match aux term with
		 | None -> None
		 | Some (base_env, ctors, rec_envl) ->
                     let env' =
                       base_env @ Env.coalesce_env p_rec_decls rec_envl @ env
                       (* @ env LUCA!!! *)
                     in
                     Some (env', ctors))

    | Ast.Default (p_some, p_none) ->  (* p_none can't bound names *)
        let p_some_decls = Env.declarations_of_term p_some in
        let p_none_decls = Env.declarations_of_term p_none in
        let p_opt_decls =
          List.filter
            (fun decl -> not (List.mem decl p_none_decls))
            p_some_decls
        in
        let none_env = List.map Env.opt_binding_of_name p_opt_decls in
        let compiled = compiler [p_some, 0] in
        (fun term env ctors ->
          match compiled term with
          | None -> Some (none_env, ctors) (* LUCA: @ env ??? *)
          | Some (env', ctors', 0) ->
              let env' =
                List.map
                  (fun (name, (ty, v)) as binding ->
                    if List.exists (fun (name', _) -> name = name') p_opt_decls
                    then Env.opt_binding_some binding
                    else binding)
                  env'
              in
              Some (env' @ env, ctors' @ ctors)
          | _ -> assert false)

    | Ast.If (p_test, p_true, p_false) ->
	let compiled_test = compiler [p_test, 0]
	and compiled_true = compiler [p_true, 0]
	and compiled_false = compiler [p_false, 0] in
	  (fun term env ctors ->
	     let branch =
	       match compiled_test term with
               | None -> compiled_false
               | Some _ -> compiled_true
	     in
             match branch term with
             | None -> None
             | Some (env', ctors', _) -> Some (env' @ env, ctors' @ ctors))

    | Ast.Fail -> (fun _ _ _ -> None)

    | _ -> assert false
end

