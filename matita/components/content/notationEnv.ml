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

(* $Id: notationEnv.ml 11104 2010-12-03 13:12:29Z asperti $ *)

module Ast = NotationPt

type ident_or_var =
   Ident of string
 | Var of string

type value =
  | TermValue of Ast.term
  | StringValue of ident_or_var
  | NumValue of string
  | OptValue of value option
  | ListValue of value list

type value_type =
  | TermType of int
  | StringType
  | NumType
  | OptType of value_type
  | ListType of value_type

exception Value_not_found of string
exception Type_mismatch of string * value_type

type declaration = string * value_type
type binding = string * (value_type * value)
type t = binding list

let lookup env name =
  try
    List.assoc name env
  with Not_found -> raise (Value_not_found name)

let lookup_value env name =
  try
    snd (List.assoc name env)
  with Not_found -> raise (Value_not_found name)

let remove_name env name = List.remove_assoc name env

let remove_names env names =
  List.filter (fun name, _ -> not (List.mem name names)) env

let lookup_term env name =
  match lookup env name with
  | _, TermValue x -> x
  | ty, _ -> raise (Type_mismatch (name, ty))

let lookup_num env name =
  match lookup env name with
  | _, NumValue x -> x
  | ty, _ -> raise (Type_mismatch (name, ty))

let lookup_string env name =
  match lookup env name with
  | _, StringValue x -> x
  | ty, _ -> raise (Type_mismatch (name, ty))

let lookup_opt env name =
  match lookup env name with
  | _, OptValue x -> x
  | ty, _ -> raise (Type_mismatch (name, ty))

let lookup_list env name =
  match lookup env name with
  | _, ListValue x -> x
  | ty, _ -> raise (Type_mismatch (name, ty))

let opt_binding_some (n, (ty, v)) = (n, (OptType ty, OptValue (Some v)))
let opt_binding_none (n, (ty, v)) = (n, (OptType ty, OptValue None))
let opt_binding_of_name (n, ty) = (n, (OptType ty, OptValue None))
let list_binding_of_name (n, ty) = (n, (ListType ty, ListValue []))
let opt_declaration (n, ty) = (n, OptType ty)
let list_declaration (n, ty) = (n, ListType ty)

let declaration_of_var = function
  | Ast.NumVar s -> s, NumType
  | Ast.IdentVar s -> s, StringType
  | Ast.TermVar (s,(Ast.Self l|Ast.Level l)) -> s, TermType l
  | _ -> assert false

let value_of_term = function
  | Ast.Num (s, _) -> NumValue s
  | Ast.Ident (s, None) -> StringValue (Var s)
  | t -> TermValue t

let term_of_value = function
  | NumValue s -> Ast.Num (s, 0)
  | StringValue (Ident s) -> Ast.Ident (s, None)
  | TermValue t -> t
  | _ -> assert false (* TO BE UNDERSTOOD *)

let rec well_typed ty value =
  match ty, value with
  | TermType _, TermValue _
  | StringType, StringValue _
  | OptType _, OptValue None
  | NumType, NumValue _ -> true
  | OptType ty', OptValue (Some value') -> well_typed ty' value'
  | ListType ty', ListValue vl ->
      List.for_all (fun value' -> well_typed ty' value') vl
  | _ -> false

let declarations_of_env = List.map (fun (name, (ty, _)) -> (name, ty))
let declarations_of_term p =
  List.map declaration_of_var (NotationUtil.variables_of_term p)

let rec combine decls values =
  match decls, values with
  | [], [] -> []
  | (name, ty) :: decls, v :: values ->
      (name, (ty, v)) :: (combine decls values)
  | _ -> assert false

let coalesce_env declarations env_list =
  let env0 = List.map list_binding_of_name declarations in
  let grow_env_entry env n v =
    List.map
      (function
        | (n', (ty, ListValue vl)) as entry ->
            if n' = n then n', (ty, ListValue (v :: vl)) else entry
        | _ -> assert false)
      env
  in
  let grow_env env_i env =
    List.fold_left
      (fun env (n, (_, v)) -> grow_env_entry env n v)
      env env_i
  in
  List.fold_right grow_env env_list env0

