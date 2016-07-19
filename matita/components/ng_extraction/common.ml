(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: common.ml 14641 2011-11-06 11:59:10Z herbelin $ i*)

open Coq
open OcamlExtractionTable
open Miniml
open Mlutil

(*s Some pretty-print utility functions. *)

let pp_par par st = if par then str "(" ++ st ++ str ")" else st

let pp_apply st par args = match args with
  | [] -> st
  | _  -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

let pr_binding = function
  | [] -> mt ()
  | l  -> str " " ++ prlist_with_sep (fun () -> str " ") pr_id l

(** By default, in module Format, you can do horizontal placing of blocks
    even if they include newlines, as long as the number of chars in the
    blocks are less that a line length. To avoid this awkward situation,
    we attach a big virtual size to [fnl] newlines. *)

let fnl () = stras (1000000,"") ++ fnl ()

let space_if = function true -> str " " | false -> mt ()

let is_invalid_id s =
 match s.[0] with 'a' .. 'z' | 'A' .. 'Z' -> false | _ -> true

let rec lowercase_id id =
 if id = "" then "x" else
 if id.[0] = '_' then lowercase_id (String.sub id 1 (String.length id - 1)) else
 if is_invalid_id id then lowercase_id ("x" ^ id) else
 String.uncapitalize id

let rec uppercase_id id =
 if id = "" then "T" else
 if id.[0] = '_' then uppercase_id (String.sub id 1 (String.length id - 1)) else
 if is_invalid_id id then uppercase_id ("x" ^ id) else
 String.capitalize id

type kind = Term | Type | Cons

let upperkind = function
  | Type
  | Term -> false
  | Cons -> true

let kindcase_id k id =
  if upperkind k then uppercase_id id else lowercase_id id

(*s de Bruijn environments for programs *)

type env = identifier list * Idset.t

(*s Generic renaming issues for local variable names. *)

let rec rename_id id avoid =
  if Idset.mem id avoid then rename_id (lift_subscript id) avoid else id

let rec rename_vars avoid = function
  | [] ->
      [], avoid
  | id :: idl when id == dummy_name ->
      (* we don't rename dummy binders *)
      let (idl', avoid') = rename_vars avoid idl in
      (id :: idl', avoid')
  | id :: idl ->
      let (idl, avoid) = rename_vars avoid idl in
      let id = rename_id (lowercase_id id) avoid in
      (id :: idl, Idset.add id avoid)

let rename_tvars avoid l =
  let rec rename avoid = function
    | [] -> [],avoid
    | id :: idl ->
	let id = rename_id (lowercase_id id) avoid in
	let idl, avoid = rename (Idset.add id avoid) idl in
	(id :: idl, avoid) in
  fst (rename avoid l)

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let get_db_name n (db,_) =
  let id = List.nth db (pred n) in
  if id = dummy_name then "__" else id

let empty_env status = [], get_global_ids status

let fake_spec = NReference.Fix (0,-1,-1)

let safe_name_of_reference status r =
 match r with
    NReference.Ref (uri, spec) when spec = fake_spec ->
     (* The field of a record *)
     NUri.name_of_uri uri
  | _ -> NCicPp.r2s status true r

let maybe_capitalize b n = if b then String.capitalize n else n

let modname_of_filename status capitalize name =
 try
  let name = modname_of_filename status name in
   status, maybe_capitalize capitalize name
 with Not_found ->
  let globs = Idset.elements (get_modnames status) in
  let s = next_ident_away (String.uncapitalize name) globs in
  let status = add_modname status s in
  let status = add_modname_for_filename status name s in
   status, maybe_capitalize capitalize s

let ref_renaming status (k,r) =
 let status,s =
  let rec ref_renaming status (k,r) =
   try status,name_of_reference status r
   with Not_found ->
   if is_projection status r then
    (* The reference for the projection and the field of a record are different
       and they would be assigned different names (name clash!). So we normalize
       the projection reference into the field reference *)
    let NReference.Ref (uri,_) = r in
    let fieldref = NReference.reference_of_spec uri fake_spec in
     ref_renaming status (k,fieldref)
   else
    let name = safe_name_of_reference status r in
    let globs = Idset.elements (get_global_ids status) in
    let s = next_ident_away (kindcase_id k name) globs in
    let status = add_global_ids status s in
    let status = add_name_for_reference status r s in
     status,s
  in
   ref_renaming status (k,r)
 in
  let baseuri = Filename.dirname (NReference.string_of_reference r) in
  if current_baseuri status = baseuri then
   status,s
  else
   let modname = Filename.basename (Filename.dirname (NReference.string_of_reference r)) in
   let status,modname = modname_of_filename status true modname in
    status, modname ^ "." ^ s

(* Main name printing function for a reference *)

let pp_global status k r = ref_renaming status (k,r)
