(* Copyright (C) 2004-2005, HELM Team.
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

(* $Id: termContentPres.ml 13019 2015-01-30 12:27:18Z fguidi $ *)

open Printf

module Ast = NotationPt
module Env = NotationEnv

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

type pattern_id = int
type pretty_printer_id = pattern_id

let resolve_binder = function
  | `Lambda -> "\\lambda"
  | `Pi -> "\\Pi"
  | `Forall -> "\\forall"
  | `Exists -> "\\exists"

let add_level_info prec t = Ast.AttributedTerm (`Level prec, t)

let rec top_pos t = add_level_info ~-1 t

let rec remove_level_info =
  function
  | Ast.AttributedTerm (`Level _, t) -> remove_level_info t
  | Ast.AttributedTerm (a, t) -> Ast.AttributedTerm (a, remove_level_info t)
  | t -> t

let add_xml_attrs attrs t =
  if attrs = [] then t else Ast.AttributedTerm (`XmlAttrs attrs, t)

let add_keyword_attrs =
  add_xml_attrs (RenderingAttrs.keyword_attributes `MathML)

let box kind spacing indent content =
  Ast.Layout (Ast.Box ((kind, spacing, indent), content))

let hbox = box Ast.H
let vbox = box Ast.V
let hvbox = box Ast.HV
let hovbox = box Ast.HOV
let break = Ast.Layout Ast.Break
let space = Ast.Literal (`Symbol " ")
let builtin_symbol s = Ast.Literal (`Symbol s)
let keyword k = add_keyword_attrs (Ast.Literal (`Keyword k))

let number s =
  add_xml_attrs (RenderingAttrs.number_attributes `MathML)
    (Ast.Literal (`Number s))

let ident i =
  add_xml_attrs (RenderingAttrs.ident_attributes `MathML) (Ast.Ident (i, None))

let ident_w_href href i =
  match href with
  | None -> ident i
  | Some href ->
      let href = NReference.string_of_reference href in
      add_xml_attrs [Some "xlink", "href", href] (ident i)

let binder_symbol s =
  add_xml_attrs (RenderingAttrs.builtin_symbol_attributes `MathML)
    (builtin_symbol s)

let xml_of_sort x = 
  let to_string x = Ast.Ident (x, None) in
  let identify x = 
    add_xml_attrs (RenderingAttrs.keyword_attributes `MathML) (to_string x)
  in
  let lvl t = Ast.AttributedTerm (`Level 90,t) in
  match x with
  | `Prop -> identify "Prop"
  | `Set -> identify "Set"
  | `CProp _ -> identify "CProp"
  | `Type _ -> identify "Type"
  | `NType s -> lvl(Ast.Layout (Ast.Sub (identify "Type",to_string s)))
  | `NCProp s -> lvl(Ast.Layout (Ast.Sub (identify "CProp",to_string s)))
;;


let map_space f l =
 HExtlib.list_concat
  ~sep:[space] (List.map (fun x -> [f x]) l)
;;

let pp_ast0 status t k =
  let rec aux =
    function
    | Ast.Appl ts ->
        let rec aux_args level =
          function
          | [] -> []
          | [ last ] ->
              [ Ast.AttributedTerm (`Level level,k last) ]
          | hd :: tl ->
              (Ast.AttributedTerm (`Level level, k hd)) :: aux_args 71 tl
        in
        add_level_info Ast.apply_prec 
          (hovbox true true (NotationUtil.dress break (aux_args 70 ts)))
    | Ast.Binder (binder_kind, (id, ty), body) ->
        add_level_info Ast.binder_prec
          (hvbox false true
            [ binder_symbol (resolve_binder binder_kind);
              k id; builtin_symbol ":"; aux_ty ty; break;
              builtin_symbol "."; k body ])
    | Ast.Case (what, indty_opt, outty_opt, patterns) ->
        let outty_box =
          match outty_opt with
          | None -> []
          | Some outty ->
              [ space; keyword "return"; space; break; remove_level_info (k outty)]
        in
        let indty_box =
          match indty_opt with
          | None -> []
          | Some (indty, href) -> [ space; keyword "in"; space; break; ident_w_href href indty ]
        in
        let match_box =
          hvbox false false [
           hvbox false false [
            hvbox false true [keyword "match"; space; break; top_pos (k what)];
            break;
            hvbox false true indty_box;
            break;
            hvbox false true outty_box
           ];
           break;
           space;
           keyword "with";
           space
         ]
        in
        let mk_case_pattern =
         function
            Ast.Pattern (head, href, vars) ->
             hvbox true true (ident_w_href href head :: 
               List.flatten (List.map (fun x -> [break;x]) (map_space aux_var vars)))
          | Ast.Wildcard -> builtin_symbol "_"
        in
        let patterns' =
          List.map
            (fun (lhs, rhs) ->
              remove_level_info
                (hovbox false true [ 
                  mk_case_pattern lhs; break; builtin_symbol "\\Rightarrow"; 
                  break; top_pos (k rhs) ]))
            patterns
        in
        let patterns'' =
          let rec aux_patterns = function
            | [] -> assert false
            | [ last ] ->
                [ break; 
                  hbox false false [
                    builtin_symbol "|";
                    last; builtin_symbol "]" ] ]
            | hd :: tl ->
                [ break; hbox false false [ builtin_symbol "|"; hd ] ]
                @ aux_patterns tl
          in
          match patterns' with
          | [] ->
              [ hbox false false [ builtin_symbol "["; builtin_symbol "]" ] ]
          | [ one ] ->
              [ hbox false false [
                builtin_symbol "["; one; builtin_symbol "]" ] ]
          | hd :: tl ->
              hbox false false [ builtin_symbol "["; hd ]
              :: aux_patterns tl
        in
        add_level_info Ast.simple_prec
          (hvbox false false [
            hvbox false false ([match_box]); break;
            hbox false false [ hvbox false false patterns'' ] ])
    | Ast.Cast (bo, ty) ->
        add_level_info Ast.simple_prec
          (hvbox false true [
            builtin_symbol "("; top_pos (k bo); break; builtin_symbol ":";
            top_pos (k ty); builtin_symbol ")"])
    | Ast.LetIn (var, s, t) ->
        add_level_info Ast.let_in_prec 
          (hvbox false true [
            hvbox false true [
              keyword "let"; space;
              hvbox false true [
                aux_var var; space;
                builtin_symbol "\\def"; break; top_pos (k s); space; keyword "in"; space ];
              ];
            break;
            k t ])
(*
    | Ast.LetRec (rec_kind, funs, where) ->
        let rec_op =
          match rec_kind with `Inductive -> "rec" | `CoInductive -> "corec"
        in
        let mk_fun (args, (name,ty), body, rec_param) =
         List.flatten (List.map (fun x -> [aux_var x; space]) args),
          k name, HExtlib.map_option k ty, k body, fst (List.nth args rec_param)
        in
        let mk_funs = List.map mk_fun in
        let fst_fun, tl_funs =
          match mk_funs funs with hd :: tl -> hd, tl | [] -> assert false
        in
        let fst_row =
          let (params, name, ty, body, rec_param) = fst_fun in
          hvbox false true ([
            keyword "let";
            space;
            keyword rec_op;
            space;
            name;
            space] @
            params @
            [keyword "on" ; space ; rec_param ;space ] @
            (match ty with None -> [] | Some ty -> [builtin_symbol ":"; ty]) @
            [ builtin_symbol "\\def";
            break;
            top_pos body ])
        in
        let tl_rows =
          List.map
            (fun (params, name, ty, body, rec_param) ->
              [ break;
                hvbox false true ([
                  keyword "and"; space;
                  name] @
                  params @
                  [space; keyword "on" ; space; rec_param ;space ] @
                  (match ty with
                      None -> []
                    | Some ty -> [builtin_symbol ":"; ty]) @
                  [ builtin_symbol "\\def"; break; body ])])
            tl_funs
        in
        add_level_info Ast.let_in_prec
          ((hvbox false false
            (fst_row :: List.flatten tl_rows
             @ [ break; keyword "in"; break; k where ])))
*)
    | Ast.Implicit `JustOne -> builtin_symbol "?"
    | Ast.Implicit `Vector -> builtin_symbol "…"
    | Ast.Meta (n, l) ->
        let local_context l =
            List.map (function None -> None | Some t -> Some (k t)) l
        in
        Ast.Meta(n, local_context l)
    | Ast.Sort sort -> aux_sort sort
    | Ast.Num _
    | Ast.Symbol _
    | Ast.Ident (_, None) | Ast.Ident (_, Some [])
    | Ast.Uri (_, None) | Ast.Uri (_, Some [])
    | Ast.Literal _
    | Ast.UserInput as leaf -> leaf
    | t -> NotationUtil.visit_ast ~special_k k t
  and aux_sort sort_kind = xml_of_sort sort_kind
  and aux_ty = function
    | None -> builtin_symbol "?"
    | Some ty -> k ty
  and aux_var = function
    | name, Some ty ->
        hvbox false true [
          builtin_symbol "("; name; builtin_symbol ":"; break; k ty;
          builtin_symbol ")" ]
    | name, None -> name
  and special_k = function
    | Ast.AttributedTerm (attrs, t) -> Ast.AttributedTerm (attrs, k t)
    | t ->
        prerr_endline ("unexpected special: " ^ NotationPp.pp_term status t);
        assert false
  in
  aux t

  (* persistent state *)

module IntMap = Map.Make(struct type t = int let compare = compare end);;

type db = {
 level1_patterns21: NotationPt.term IntMap.t;
 compiled21: ((NotationPt.term -> (NotationEnv.t * NotationPt.term list * int) option)) Lazy.t;
 pattern21_matrix: (NotationPt.term * pattern_id) list;
 counter: pattern_id
}

let initial_db = {
 level1_patterns21 = IntMap.empty;
 compiled21 = lazy (Content2presMatcher.Matcher21.compiler []);
 pattern21_matrix = [];
 counter = ~-1 
}

class type g_status =
  object
    method content_pres_db: db
  end
 
class virtual status =
 object
   inherit NCic.status
   val content_pres_db = initial_db  
   method content_pres_db = content_pres_db
   method set_content_pres_db v = {< content_pres_db = v >}
   method set_content_pres_status
    : 'status. #g_status as 'status -> 'self
    = fun o -> {< content_pres_db = o#content_pres_db >}
 end

let get_compiled21 status =
  Lazy.force status#content_pres_db.compiled21

let set_compiled21 status f =
 status#set_content_pres_db
  { status#content_pres_db with compiled21 = f }

let add_idrefs =
  List.fold_right (fun idref t -> Ast.AttributedTerm (`IdRef idref, t))

let instantiate21 idrefs env l1 =
  let rec subst_singleton pos env =
    function
      Ast.AttributedTerm (attr, t) ->
        Ast.AttributedTerm (attr, subst_singleton pos env t)
    | t -> NotationUtil.group (subst pos env t)
  and subst pos env = function
    | Ast.AttributedTerm (attr, t) ->
(*         prerr_endline ("loosing attribute " ^ NotationPp.pp_attribute attr); *)
        subst pos env t
    | Ast.Variable var ->
        let name, expected_ty = NotationEnv.declaration_of_var var in
        let ty, value =
          try
            List.assoc name env
          with Not_found ->
            prerr_endline ("name " ^ name ^ " not found in environment");
            assert false
        in
        assert (NotationEnv.well_typed ty value); (* INVARIANT *)
        (* following assertion should be a conditional that makes this
         * instantiation fail *)
        if not (NotationEnv.well_typed expected_ty value) then
         begin
          prerr_endline ("The variable " ^ name ^ " is used with the wrong type in the notation declaration");
          assert false
         end;
        let value = NotationEnv.term_of_value value in
        let value = 
          match expected_ty with
          | Env.TermType l -> Ast.AttributedTerm (`Level l,value) 
          | _ -> value
        in
        [ value ]
    | Ast.Magic m -> subst_magic pos env m
    | Ast.Literal l as t ->
        let t = add_idrefs idrefs t in
        (match l with
        | `Keyword k -> [ add_keyword_attrs t ]
        | _ -> [ t ])
    | Ast.Layout l -> [ Ast.Layout (subst_layout pos env l) ]
    | t -> [ NotationUtil.visit_ast (subst_singleton pos env) t ]
  and subst_magic pos env = function
    | Ast.List0 (p, sep_opt)
    | Ast.List1 (p, sep_opt) ->
        let rec_decls = NotationEnv.declarations_of_term p in
        let rec_values =
          List.map (fun (n, _) -> NotationEnv.lookup_list env n) rec_decls
        in
        let values = NotationUtil.ncombine rec_values in
        let sep =
          match sep_opt with
            | None -> []
            | Some l -> [ Ast.Literal l; break; space ]
	in
        let rec instantiate_list acc = function
          | [] -> List.rev acc
	  | value_set :: [] ->
	      let env = NotationEnv.combine rec_decls value_set in
              instantiate_list (NotationUtil.group (subst pos env p) :: acc)
                []
          | value_set :: tl ->
              let env = NotationEnv.combine rec_decls value_set in
              let terms = subst pos env p in
              instantiate_list (NotationUtil.group (terms @ sep) :: acc) tl
        in
        if values = [] then []
        else [hovbox false false (instantiate_list [] values)]
    | Ast.Opt p ->
        let opt_decls = NotationEnv.declarations_of_term p in
        let env =
          let rec build_env = function
            | [] -> []
            | (name, ty) :: tl ->
                  (* assumption: if one of the value is None then all are *)
                (match NotationEnv.lookup_opt env name with
                | None -> raise Exit
                | Some v -> (name, (ty, v)) :: build_env tl)
          in
          try build_env opt_decls with Exit -> []
        in
	  begin
	    match env with
	      | [] -> []
	      | _ -> subst pos env p
	  end
    | _ -> assert false (* impossible *)
  and subst_layout pos env = function
    | Ast.Box (kind, tl) ->
        let tl' = subst_children pos env tl in
        Ast.Box (kind, List.concat tl')
    | l -> NotationUtil.visit_layout (subst_singleton pos env) l
  and subst_children pos env =
    function
    | [] -> []
    | [ child ] ->
        let pos' =
          match pos with
          | `Inner -> `Right
          | `Left -> `Left
(*           | `None -> assert false *)
          | `Right -> `Right
        in
        [ subst pos' env child ]
    | hd :: tl ->
        let pos' =
          match pos with
          | `Inner -> `Inner
          | `Left -> `Inner
(*           | `None -> assert false *)
          | `Right -> `Right
        in
        (subst pos env hd) :: subst_children pos' env tl
  in
    subst_singleton `Left env l1

let rec pp_ast1 status term = 
  let rec pp_value = function
    | NotationEnv.NumValue _ as v -> v
    | NotationEnv.StringValue _ as v -> v
(*     | NotationEnv.TermValue t when t == term -> NotationEnv.TermValue (pp_ast0 status t pp_ast1) *)
    | NotationEnv.TermValue t -> NotationEnv.TermValue (pp_ast1 status t)
    | NotationEnv.OptValue None as v -> v
    | NotationEnv.OptValue (Some v) -> 
        NotationEnv.OptValue (Some (pp_value v))
    | NotationEnv.ListValue vl ->
        NotationEnv.ListValue (List.map pp_value vl)
  in
  let ast_env_of_env env =
    List.map (fun (var, (ty, value)) -> (var, (ty, pp_value value))) env
  in
(* prerr_endline ("pattern matching from 2 to 1 on term " ^ NotationPp.pp_term term); *)
  match term with
  | Ast.AttributedTerm (attrs, term') ->
      Ast.AttributedTerm (attrs, pp_ast1 status term')
  | _ ->
      (match get_compiled21 status term with
      | None -> pp_ast0 status term (pp_ast1 status)
      | Some (env, ctors, pid) ->
          let idrefs =
            List.flatten (List.map NotationUtil.get_idrefs ctors)
          in
          let l1 =
            try
              IntMap.find pid status#content_pres_db.level1_patterns21
            with Not_found -> assert false
          in
          instantiate21 idrefs (ast_env_of_env env) l1)

let load_patterns21 status t =
  set_compiled21 status (lazy (Content2presMatcher.Matcher21.compiler t))

let pp_ast status ast =
  debug_print (lazy "pp_ast <-");
  let ast' = pp_ast1 status ast in
  debug_print (lazy ("pp_ast -> " ^ NotationPp.pp_term status ast'));
  ast'

let fill_pos_info l1_pattern = l1_pattern
(*   let rec aux toplevel pos =
    function
    | Ast.Layout l ->
        (match l 

    | Ast.Magic m ->
        Ast.Box (
    | Ast.Variable _ as t -> add_pos_info pos t
    | t -> t
  in
  aux true l1_pattern *)

let fresh_id status =
  let counter = status#content_pres_db.counter+1 in
   status#set_content_pres_db ({ status#content_pres_db with counter = counter  }), counter

let add_pretty_printer status l2 (CicNotationParser.CL1P (l1,precedence)) =
  let status,id = fresh_id status in
  let l1' = add_level_info precedence (fill_pos_info l1) in
  let l2' = NotationUtil.strip_attributes l2 in
  let status =
   status#set_content_pres_db
    { status#content_pres_db with
       level1_patterns21 =
        IntMap.add id l1' status#content_pres_db.level1_patterns21;
       pattern21_matrix = (l2',id)::status#content_pres_db.pattern21_matrix } in
  load_patterns21 status status#content_pres_db.pattern21_matrix 

  (* presentation -> content *)

let unopt_names names env =
  let rec aux acc = function
    | (name, (ty, v)) :: tl when List.mem name names ->
        (match ty, v with
        | Env.OptType ty, Env.OptValue (Some v) ->
            aux ((name, (ty, v)) :: acc) tl
        | _ -> assert false)
    | hd :: tl -> aux (hd :: acc) tl
    | [] -> acc
  in
  aux [] env

let head_names names env =
  let rec aux acc = function
    | (name, (ty, v)) :: tl when List.mem name names ->
        (match ty, v with
        | Env.ListType ty, Env.ListValue (v :: _) ->
            aux ((name, (ty, v)) :: acc) tl
        | Env.TermType _, Env.TermValue _  ->
            aux ((name, (ty, v)) :: acc) tl
        | Env.OptType _, Env.OptValue _ ->
            aux ((name, (ty, v)) :: acc) tl
        | _ -> assert false)
    | _ :: tl -> aux acc tl
      (* base pattern may contain only meta names, thus we trash all others *)
    | [] -> acc
  in
  aux [] env

let tail_names names env =
  let rec aux acc = function
    | (name, (ty, v)) :: tl when List.mem name names ->
        (match ty, v with
        | Env.ListType ty, Env.ListValue (_ :: vtl) ->
            aux ((name, (Env.ListType ty, Env.ListValue vtl)) :: acc) tl
        | Env.TermType _, Env.TermValue _  ->
            aux ((name, (ty, v)) :: acc) tl
        | Env.OptType _, Env.OptValue _ ->
            aux ((name, (ty, v)) :: acc) tl
        | _ -> assert false)
    | binding :: tl -> aux (binding :: acc) tl
    | [] -> acc
  in
  aux [] env

let instantiate_level2 status env term =
(*   prerr_endline ("istanzio: " ^ NotationPp.pp_term term); *)
  let fresh_env = ref [] in
  let lookup_fresh_name n =
    try
      List.assoc n !fresh_env
    with Not_found ->
      let new_name = NotationUtil.fresh_name () in
      fresh_env := (n, new_name) :: !fresh_env;
      new_name
  in
  let rec aux env term =
    match term with
    | Ast.AttributedTerm (a, term) -> (*Ast.AttributedTerm (a, *)aux env term
    | Ast.Appl terms -> Ast.Appl (List.map (aux env) terms)
    | Ast.Binder (binder, var, body) ->
        Ast.Binder (binder, aux_capture_var env var, aux env body)
    | Ast.Case (term, indty, outty_opt, patterns) ->
        Ast.Case (aux env term, indty, aux_opt env outty_opt,
          List.map (aux_branch env) patterns)
    | Ast.LetIn (var, t1, t3) ->
        Ast.LetIn (aux_capture_var env var, aux env t1, aux env t3)
(*    
    | Ast.LetRec (kind, definitions, body) ->
        Ast.LetRec (kind, List.map (aux_definition env) definitions,
          aux env body)
*)    
    | Ast.Uri (name, None) -> Ast.Uri (name, None)
    | Ast.Uri (name, Some substs) ->
        Ast.Uri (name, Some (aux_substs env substs))
    | Ast.Ident (name, Some substs) ->
        Ast.Ident (name, Some (aux_substs env substs))
    | Ast.Meta (index, substs) -> Ast.Meta (index, aux_meta_substs env substs)

    | Ast.Implicit _
    | Ast.Ident _
    | Ast.Num _
    | Ast.Sort _
    | Ast.Symbol _
    | Ast.UserInput -> term

    | Ast.Magic magic -> aux_magic env magic
    | Ast.Variable var -> aux_variable env var

    | Ast.Cast (t, ty) -> Ast.Cast (aux env t, aux env ty)

    | _ -> assert false
  and aux_opt env = function
    | Some term -> Some (aux env term)
    | None -> None
  and aux_capture_var env (name, ty_opt) = (aux env name, aux_opt env ty_opt)
  and aux_branch env (pattern, term) =
    (aux_pattern env pattern, aux env term)
  and aux_pattern env =
   function
      Ast.Pattern (head, hrefs, vars) ->
       Ast.Pattern (head, hrefs, List.map (aux_capture_var env) vars)
    | Ast.Wildcard -> Ast.Wildcard
  and aux_definition env (params, var, term, i) =
    (List.map (aux_capture_var env) params, aux_capture_var env var, aux env term, i)
  and aux_substs env substs =
    List.map (fun (name, term) -> (name, aux env term)) substs
  and aux_meta_substs env meta_substs = List.map (aux_opt env) meta_substs
  and aux_variable env = function
    | Ast.NumVar name -> Ast.Num (Env.lookup_num env name, 0)
    | Ast.IdentVar name ->
       (match Env.lookup_string env name with
           Env.Ident x -> Ast.Ident (x, None)
         | Env.Var x -> Ast.Variable (Ast.IdentVar x))
    | Ast.TermVar (name,(Ast.Level l|Ast.Self l)) -> 
        Ast.AttributedTerm (`Level l,Env.lookup_term env name)
    | Ast.FreshVar name -> Ast.Ident (lookup_fresh_name name, None)
    | Ast.Ascription (term, name) -> assert false
  and aux_magic env = function
    | Ast.Default (some_pattern, none_pattern) ->
        let some_pattern_names = NotationUtil.names_of_term some_pattern in
        let none_pattern_names = NotationUtil.names_of_term none_pattern in
        let opt_names =
          List.filter
            (fun name -> not (List.mem name none_pattern_names))
            some_pattern_names
        in
        (match opt_names with
        | [] -> assert false (* some pattern must contain at least 1 name *)
        | (name :: _) as names ->
            (match Env.lookup_value env name with
            | Env.OptValue (Some _) ->
                (* assumption: if "name" above is bound to Some _, then all
                 * names returned by "meta_names_of" are bound to Some _ as well
                 *)
                aux (unopt_names names env) some_pattern
            | Env.OptValue None -> aux env none_pattern
            | _ ->
                prerr_endline (sprintf
                  "lookup of %s in env %s did not return an optional value"
                  name (NotationPp.pp_env status env));
                assert false))
    | Ast.Fold (`Left, base_pattern, names, rec_pattern) ->
        let acc_name = List.hd names in (* names can't be empty, cfr. parser *)
        let meta_names =
          List.filter ((<>) acc_name)
            (NotationUtil.names_of_term rec_pattern)
        in
        (match meta_names with
        | [] -> assert false (* as above *)
        | (name :: _) as names ->
            let rec instantiate_fold_left acc env' =
              match Env.lookup_value env' name with
              | Env.ListValue (_ :: _) ->
                  instantiate_fold_left 
                    (let acc_binding =
                      acc_name, (Env.TermType 0, Env.TermValue acc)
                     in
                     aux (acc_binding :: head_names names env') rec_pattern)
                    (tail_names names env')
              | Env.ListValue [] -> acc
              | _ -> assert false
            in
            instantiate_fold_left (aux env base_pattern) env)
    | Ast.Fold (`Right, base_pattern, names, rec_pattern) ->
        let acc_name = List.hd names in (* names can't be empty, cfr. parser *)
        let meta_names =
          List.filter ((<>) acc_name)
            (NotationUtil.names_of_term rec_pattern)
        in
        (match meta_names with
        | [] -> assert false (* as above *)
        | (name :: _) as names ->
            let rec instantiate_fold_right env' =
              match Env.lookup_value env' name with
              | Env.ListValue (_ :: _) ->
                  let acc = instantiate_fold_right (tail_names names env') in
                  let acc_binding =
                    acc_name, (Env.TermType 0, Env.TermValue acc)
                  in
                  aux (acc_binding :: head_names names env') rec_pattern
              | Env.ListValue [] -> aux env base_pattern
              | _ -> assert false
            in
            instantiate_fold_right env)
    | Ast.If (_, p_true, p_false) as t ->
        aux env (NotationUtil.find_branch (Ast.Magic t))
    | Ast.Fail -> assert false
    | _ -> assert false
  in
  aux env term
