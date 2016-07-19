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

(* $Id: notationUtil.ml 13145 2016-03-13 17:30:14Z fguidi $ *)

module Ast = NotationPt

let visit_ast ?(special_k = fun _ -> assert false) 
  ?(map_xref_option= fun x -> x) ?(map_case_indty= fun x -> x) 
  ?(map_case_outtype=
      fun k x -> match x with None -> None | Some x -> Some (k x)) 
  k 
=
  let rec aux = function
    | Ast.Appl terms -> Ast.Appl (List.map k terms)
    | Ast.Binder (kind, var, body) ->
        Ast.Binder (kind, aux_capture_variable var, k body) 
    | Ast.Case (term, indtype, typ, patterns) ->
        Ast.Case (k term, map_case_indty indtype, map_case_outtype k typ,
          aux_patterns map_xref_option patterns)
    | Ast.Cast (t1, t2) -> Ast.Cast (k t1, k t2)
    | Ast.LetIn (var, t1, t3) ->
        Ast.LetIn (aux_capture_variable var, k t1, k t3)
    | Ast.Ident (name, Some substs) ->
        Ast.Ident (name, Some (aux_substs substs))
    | Ast.Uri (name, Some substs) -> Ast.Uri (name, Some (aux_substs substs))
    | Ast.Meta (index, substs) -> Ast.Meta (index, List.map aux_opt substs)
    | (Ast.AttributedTerm _
      | Ast.Layout _
      | Ast.Literal _
      | Ast.Magic _
      | Ast.Variable _) as t -> special_k t
    | (Ast.Ident _
      | Ast.NRef _
      | Ast.NCic _
      | Ast.Implicit _
      | Ast.Num _
      | Ast.Sort _
      | Ast.Symbol _
      | Ast.Uri _
      | Ast.UserInput) as t -> t
  and aux_opt = function
    | None -> None
    | Some term -> Some (k term)
  and aux_capture_variable (term, typ_opt) = k term, aux_opt typ_opt
  and aux_patterns k_xref patterns = List.map (aux_pattern k_xref) patterns
  and aux_pattern k_xref =
   function
      Ast.Pattern (head, hrefs, vars), term ->
        Ast.Pattern (head, k_xref hrefs, List.map aux_capture_variable vars), k term
    | Ast.Wildcard, term -> Ast.Wildcard, k term
  and aux_subst (name, term) = (name, k term)
  and aux_substs substs = List.map aux_subst substs
  in
  aux

let visit_layout k = function
  | Ast.Sub (t1, t2) -> Ast.Sub (k t1, k t2)
  | Ast.Sup (t1, t2) -> Ast.Sup (k t1, k t2)
  | Ast.Below (t1, t2) -> Ast.Below (k t1, k t2)
  | Ast.Above (t1, t2) -> Ast.Above (k t1, k t2)
  | Ast.Over (t1, t2) -> Ast.Over (k t1, k t2)
  | Ast.Atop (t1, t2) -> Ast.Atop (k t1, k t2)
  | Ast.Frac (t1, t2) -> Ast.Frac (k t1, k t2)
  | Ast.InfRule (t1, t2, t3) -> Ast.InfRule (k t1, k t2, k t3)
  | Ast.Sqrt t -> Ast.Sqrt (k t)
  | Ast.Root (arg, index) -> Ast.Root (k arg, k index)
  | Ast.Break -> Ast.Break
  | Ast.Box (kind, terms) -> Ast.Box (kind, List.map k terms)
  | Ast.Group terms -> Ast.Group (List.map k terms)
  | Ast.Mstyle (l, term) -> Ast.Mstyle (l, List.map k term)
  | Ast.Mpadded (l, term) -> Ast.Mpadded (l, List.map k term)
  | Ast.Maction terms -> Ast.Maction (List.map k terms)

let visit_magic k = function
  | Ast.List0 (t, l) -> Ast.List0 (k t, l)
  | Ast.List1 (t, l) -> Ast.List1 (k t, l)
  | Ast.Opt t -> Ast.Opt (k t)
  | Ast.Fold (kind, t1, names, t2) -> Ast.Fold (kind, k t1, names, k t2)
  | Ast.Default (t1, t2) -> Ast.Default (k t1, k t2)
  | Ast.If (t1, t2, t3) -> Ast.If (k t1, k t2, k t3)
  | Ast.Fail -> Ast.Fail

let visit_variable k = function
  | Ast.NumVar _
  | Ast.IdentVar _
  | Ast.TermVar _
  | Ast.FreshVar _ as t -> t
  | Ast.Ascription (t, s) -> Ast.Ascription (k t, s)

let variables_of_term t =
  let rec vars = ref [] in
  let add_variable v =
    if List.mem v !vars then ()
    else vars := v :: !vars
  in
  let rec aux = function
    | Ast.Magic m -> Ast.Magic (visit_magic aux m)
    | Ast.Layout l -> Ast.Layout (visit_layout aux l)
    | Ast.Variable v -> Ast.Variable (aux_variable v)
    | Ast.Literal _ as t -> t
    | Ast.AttributedTerm (_, t) -> aux t
    | t -> visit_ast aux t
  and aux_variable = function
    | (Ast.NumVar _
      | Ast.IdentVar _
      | Ast.TermVar _) as t ->
	add_variable t ;
	t
    | Ast.FreshVar _ as t -> t
    | Ast.Ascription _ -> assert false
  in
    ignore (aux t) ;
    !vars

let names_of_term t =
  let aux = function
    | Ast.NumVar s
    | Ast.IdentVar s
    | Ast.TermVar (s,_) -> s
    | _ -> assert false
  in
    List.map aux (variables_of_term t)

let keywords_of_term t =
  let rec keywords = ref [] in
  let add_keyword k = keywords := k :: !keywords in
  let rec aux = function
    | Ast.AttributedTerm (_, t) -> aux t
    | Ast.Layout l -> Ast.Layout (visit_layout aux l)
    | Ast.Literal (`Keyword k) as t ->
        add_keyword k;
        t
    | Ast.Literal _ as t -> t
    | Ast.Magic m -> Ast.Magic (visit_magic aux m)
    | Ast.Variable _ as v -> v
    | t -> visit_ast aux t
  in
    ignore (aux t) ;
    !keywords

let rec strip_attributes t =
  let special_k = function
    | Ast.AttributedTerm (_, term) -> strip_attributes term
    | Ast.Magic m -> Ast.Magic (visit_magic strip_attributes m)
    | Ast.Variable _ as t -> t
    | t -> assert false
  in
  visit_ast ~special_k strip_attributes t

let rec get_idrefs =
  function
  | Ast.AttributedTerm (`IdRef id, t) -> id :: get_idrefs t
  | Ast.AttributedTerm (_, t) -> get_idrefs t
  | _ -> []

let meta_names_of_term term =
  let rec names = ref [] in
  let add_name n =
    if List.mem n !names then ()
    else names := n :: !names
  in
  let rec aux = function
    | Ast.AttributedTerm (_, term) -> aux term
    | Ast.Appl terms -> List.iter aux terms
    | Ast.Binder (_, _, body) -> aux body
    | Ast.Case (term, indty, outty_opt, patterns) ->
        aux term ;
        aux_opt outty_opt ;
        List.iter aux_branch patterns
    | Ast.LetIn (_, t1, t3) ->
        aux t1 ;
        aux t3
    | Ast.Uri (_, Some substs) -> aux_substs substs
    | Ast.Ident (_, Some substs) -> aux_substs substs
    | Ast.Meta (_, substs) -> aux_meta_substs substs

    | Ast.Implicit _
    | Ast.Ident _
    | Ast.Num _
    | Ast.Sort _
    | Ast.Symbol _
    | Ast.Uri _
    | Ast.UserInput -> ()

    | Ast.Magic magic -> aux_magic magic
    | Ast.Variable var -> aux_variable var

    | _ -> assert false
  and aux_opt = function
    | Some term -> aux term
    | None -> ()
  and aux_capture_var (_, ty_opt) = aux_opt ty_opt
  and aux_branch (pattern, term) =
    aux_pattern pattern ;
    aux term
  and aux_pattern =
   function
      Ast.Pattern (head, _, vars) -> List.iter aux_capture_var vars
    | Ast.Wildcard -> ()
  and aux_substs substs = List.iter (fun (_, term) -> aux term) substs
  and aux_meta_substs meta_substs = List.iter aux_opt meta_substs
  and aux_variable = function
    | Ast.NumVar name -> add_name name
    | Ast.IdentVar name -> add_name name
    | Ast.TermVar (name,_) -> add_name name
    | Ast.FreshVar _ -> ()
    | Ast.Ascription _ -> assert false
  and aux_magic = function
    | Ast.Default (t1, t2)
    | Ast.Fold (_, t1, _, t2) ->
        aux t1 ;
        aux t2
    | Ast.If (t1, t2, t3) ->
        aux t1 ;
        aux t2 ;
	aux t3
    | Ast.Fail -> ()
    | _ -> assert false
  in
  aux term ;
  !names

let rectangular matrix =
  let columns = Array.length matrix.(0) in
  try
    Array.iter (fun a -> if Array.length a <> columns then raise Exit) matrix;
    true
  with Exit -> false

let ncombine ll =
  let matrix = Array.of_list (List.map Array.of_list ll) in
  assert (rectangular matrix);
  let rows = Array.length matrix in
  let columns = Array.length matrix.(0) in
  let lists = ref [] in
  for j = 0 to columns - 1 do
    let l = ref [] in
    for i = 0 to rows - 1 do
      l := matrix.(i).(j) :: !l
    done;
    lists := List.rev !l :: !lists
  done;
  List.rev !lists

let string_of_literal = function
  | `Symbol s
  | `Keyword s
  | `Number s -> s

let boxify = function
  | [ a ] -> a
  | l -> Ast.Layout (Ast.Box ((Ast.H, false, false), l))

let unboxify = function
  | Ast.Layout (Ast.Box ((Ast.H, false, false), [ a ])) -> a
  | l -> l

let group = function
  | [ a ] -> a
  | l -> Ast.Layout (Ast.Group l)

let ungroup =
  let rec aux acc =
    function
	[] -> List.rev acc
      | Ast.Layout (Ast.Group terms) :: terms' -> aux acc (terms @ terms')
      | term :: terms -> aux (term :: acc) terms
  in
    aux []

let dress ~sep:sauce =
  let rec aux =
    function
      | [] -> []
      | [hd] -> [hd]
      | hd :: tl -> hd :: sauce :: aux tl
  in
    aux

let dressn ~sep:sauces =
  let rec aux =
    function
      | [] -> []
      | [hd] -> [hd]
      | hd :: tl -> hd :: sauces @ aux tl
  in
    aux

let find_appl_pattern_uris ap =
  let rec aux acc =
    function
    | Ast.NRefPattern nref -> nref :: acc
    | Ast.ImplicitPattern
    | Ast.VarPattern _ -> acc
    | Ast.ApplPattern apl -> List.fold_left aux acc apl
  in
  let uris = aux [] ap in
  HExtlib.list_uniq (List.fast_sort NReference.compare uris)

let rec find_branch =
  function
      Ast.Magic (Ast.If (_, Ast.Magic Ast.Fail, t)) -> find_branch t
    | Ast.Magic (Ast.If (_, t, _)) -> find_branch t
    | t -> t

let fresh_index = ref ~-1

type notation_id = int

let fresh_id () =
  incr fresh_index;
  !fresh_index

  (* TODO ensure that names generated by fresh_var do not clash with user's *)
  (* FG: "η" is not an identifier (it is rendered, but not parsed) *)
let fresh_name () = "eta" ^ string_of_int (fresh_id ())

let rec freshen_term ?(index = ref 0) term =
  let freshen_term = freshen_term ~index in
  let fresh_instance () = incr index; !index in
  let special_k = function
    | Ast.AttributedTerm (attr, t) -> Ast.AttributedTerm (attr, freshen_term t)
    | Ast.Layout l -> Ast.Layout (visit_layout freshen_term l)
    | Ast.Magic m -> Ast.Magic (visit_magic freshen_term m)
    | Ast.Variable v -> Ast.Variable (visit_variable freshen_term v)
    | Ast.Literal _ as t -> t
    | _ -> assert false
  in
  match term with
  | Ast.Symbol (s, instance) -> Ast.Symbol (s, fresh_instance ())
  | Ast.Num (s, instance) -> Ast.Num (s, fresh_instance ())
  | t -> visit_ast ~special_k freshen_term t

let freshen_obj obj =
  let index = ref 0 in
  let freshen_term = freshen_term ~index in
  let freshen_name_ty = List.map (fun (n, t) -> (n, freshen_term t)) in
  let freshen_name_ty_b = List.map (fun (n,t,b,i) -> (n,freshen_term t,b,i)) in
  let freshen_capture_variable (n, t) = freshen_term n, HExtlib.map_option freshen_term t in 
  let freshen_capture_variables = List.map freshen_capture_variable in
  match obj with
  | NotationPt.Inductive (params, indtypes, attrs) ->
      let indtypes =
        List.map
          (fun (n, co, ty, ctors) -> (n, co, ty, freshen_name_ty ctors))
          indtypes
      in
      NotationPt.Inductive (freshen_capture_variables params, indtypes, attrs)
  | NotationPt.Theorem (n, t, ty_opt, attrs) ->
      let ty_opt =
        match ty_opt with None -> None | Some ty -> Some (freshen_term ty)
      in
      NotationPt.Theorem (n, freshen_term t, ty_opt, attrs)
  | NotationPt.Record (params, n, ty, fields, attrs) ->
      NotationPt.Record (freshen_capture_variables params, n,
        freshen_term ty, freshen_name_ty_b fields, attrs)
  | NotationPt.LetRec (kind, definitions, attrs) ->
      let definitions =
        List.map
          (fun (params, var, ty, decrno) ->
            freshen_capture_variables params, freshen_capture_variable var,
            freshen_term ty, decrno)
          definitions
      in
      NotationPt.LetRec (kind, definitions, attrs)

let freshen_term = freshen_term ?index:None

let rec refresh_uri_in_term ~refresh_uri_in_term:refresh_in_cic
 ~refresh_uri_in_reference
=
 function
    NotationPt.NRef ref -> NotationPt.NRef (refresh_uri_in_reference ref)
  | NotationPt.NCic t -> NotationPt.NCic (refresh_in_cic t)
  | t ->
     visit_ast
     (refresh_uri_in_term ~refresh_uri_in_term:refresh_in_cic
       ~refresh_uri_in_reference) t
      ~special_k:(fun x -> x)
      ~map_xref_option:(function Some ref -> Some (refresh_uri_in_reference ref)
                         | x -> x)
      ~map_case_indty:(function (Some (s,Some ref)) -> Some (s, Some
                        (refresh_uri_in_reference ref)) | x -> x)
;;
