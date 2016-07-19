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

(* $Id: notationPp.ml 13180 2016-04-27 16:25:05Z fguidi $ *)

open Printf

module Ast = NotationPt
module Env = NotationEnv

  (* when set to true debugging information, not in sync with input syntax, will
   * be added to the output of pp_term.
   * set to false if you need, for example, cut and paste from matitac output to
   * matitatop *)
let debug_printing = false

let pp_binder = function
  | `Lambda -> "lambda"
  | `Pi -> "Pi"
  | `Exists -> "exists"
  | `Forall -> "forall"

let pp_literal =
  if debug_printing then
    (function (* debugging version *)
      | `Symbol s -> sprintf "symbol(%s)" s
      | `Keyword s -> sprintf "keyword(%s)" s
      | `Number s -> sprintf "number(%s)" s)
  else
    (function
      | `Symbol s
      | `Keyword s
      | `Number s -> s)

let pp_pos =
  function
(*      `None -> "`None" *)
    | `Left -> "`Left"
    | `Right -> "`Right"
    | `Inner -> "`Inner"

let pp_attribute =
  function
  | `IdRef id -> sprintf "x(%s)" id
  | `XmlAttrs attrs ->
      sprintf "X(%s)"
        (String.concat ";"
          (List.map (fun (_, n, v) -> sprintf "%s=%s" n v) attrs))
  | `Level (prec) -> sprintf "L(%d)" prec 
  | `Raw _ -> "R"
  | `Loc _ -> "@"
  | `ChildPos p -> sprintf "P(%s)" (pp_pos p)

let pp_capture_variable pp_term = 
  function
  | term, None -> pp_term (* ~pp_parens:false *) term
  | term, Some typ -> "(" ^ pp_term (* ~pp_parens:false *) term ^ ": " ^ pp_term typ ^ ")"

let rec pp_term (status : #NCic.status) ?(pp_parens = true) t =
  let pp_term = pp_term status in
  let t_pp =
    match t with
    | Ast.AttributedTerm (attr, term) when debug_printing ->
        sprintf "%s[%s]" (pp_attribute attr) (pp_term ~pp_parens:false term)
    | Ast.AttributedTerm (`Raw text, _) -> text
    | Ast.AttributedTerm (_, term) -> pp_term ~pp_parens:false term
    | Ast.Appl terms ->
        sprintf "%s" (String.concat " " (List.map pp_term terms))
    | Ast.Binder (`Forall, (Ast.Ident ("_", None), typ), body)
    | Ast.Binder (`Pi, (Ast.Ident ("_", None), typ), body) ->
        sprintf "%s \\to %s"
          (match typ with None -> "?" | Some typ -> pp_term typ)
          (pp_term ~pp_parens:true body)
    | Ast.Binder (kind, var, body) ->
        sprintf "\\%s %s.%s" (pp_binder kind) (pp_capture_variable pp_term var)
          (pp_term ~pp_parens:true body)
    | Ast.Case (term, indtype, typ, patterns) ->
        sprintf "match %s%s%s with %s"
          (pp_term term)
          (match indtype with
          | None -> ""
          | Some (ty, href_opt) ->
              sprintf " in %s%s" ty
              (match debug_printing, href_opt with
              | true, Some uri ->
                  sprintf "(i.e.%s)" (NReference.string_of_reference uri)
              | _ -> ""))	  
	  (match typ with None -> "" | Some t -> sprintf " return %s" (pp_term t))          
          (pp_patterns status patterns)
    | Ast.Cast (t1, t2) -> sprintf "(%s: %s)" (pp_term ~pp_parens:true t1) (pp_term ~pp_parens:true t2)
    | Ast.LetIn ((var,t2), t1, t3) ->
(*       let t2 = match t2 with None -> Ast.Implicit | Some t -> t in *)
        sprintf "let %s \\def %s in %s" (pp_term var)
(*           (pp_term ~pp_parens:true t2) *)
          (pp_term ~pp_parens:true t1)
          (pp_term ~pp_parens:true t3)
    | Ast.Ident (name, Some []) | Ast.Ident (name, None)
    | Ast.Uri (name, Some []) | Ast.Uri (name, None) -> name
    | Ast.NRef nref -> NReference.string_of_reference nref
    | Ast.NCic cic -> status#ppterm ~metasenv:[] ~context:[] ~subst:[] cic
    | Ast.Ident (name, Some substs)
    | Ast.Uri (name, Some substs) ->
        sprintf "%s \\subst [%s]" name (pp_substs status substs)
    | Ast.Implicit `Vector -> "…"
    | Ast.Implicit `JustOne -> "?"
    | Ast.Implicit (`Tagged name) -> "?"^name
    | Ast.Meta (index, substs) ->
        sprintf "%d[%s]" index
          (String.concat "; "
            (List.map (function None -> "?" | Some t -> pp_term t) substs))
    | Ast.Num (num, _) -> num
    | Ast.Sort `Set -> "Set"
    | Ast.Sort `Prop -> "Prop"
    | Ast.Sort (`NType s)-> "Type[" ^ s ^ "]"
    | Ast.Sort (`NCProp s)-> "CProp[" ^ s ^ "]"
    | Ast.Symbol (name, _) -> "'" ^ name

    | Ast.UserInput -> "%"

    | Ast.Literal l -> pp_literal l
    | Ast.Layout l -> pp_layout status l
    | Ast.Magic m -> pp_magic status m
    | Ast.Variable v -> pp_variable v
  in
  match pp_parens, t with
    | false, _ 
    | true, Ast.Implicit _
    | true, Ast.UserInput
    | true, Ast.Sort _
    | true, Ast.Ident (_, Some []) 
    | true, Ast.Ident (_, None)    -> t_pp
    | _                            -> sprintf "(%s)" t_pp

and pp_subst status (name, term) =
 sprintf "%s \\Assign %s" name (pp_term status term)
and pp_substs status substs = String.concat "; " (List.map (pp_subst status) substs)

and pp_pattern status =
 function
    Ast.Pattern (head, href, vars), term ->
     let head_pp =
       head ^
       (match debug_printing, href with
       | true, Some uri -> sprintf "(i.e.%s)" (NReference.string_of_reference uri)
       | _ -> "")
     in
     sprintf "%s \\Rightarrow %s"
       (match vars with
       | [] -> head_pp
       | _ ->
           sprintf "(%s %s)" head_pp
             (String.concat " " (List.map (pp_capture_variable (pp_term status)) vars)))
       (pp_term status term)
  | Ast.Wildcard, term ->
     sprintf "_ \\Rightarrow %s" (pp_term status term)

and pp_patterns status patterns =
  sprintf "[%s]" (String.concat " | " (List.map (pp_pattern status) patterns))

and pp_box_spec (kind, spacing, indent) =
  let int_of_bool b = if b then 1 else 0 in
  let kind_string =
    match kind with
    Ast.H -> "H" | Ast.V -> "V" | Ast.HV -> "HV" | Ast.HOV -> "HOV"
  in
  sprintf "%sBOX%d%d" kind_string (int_of_bool spacing) (int_of_bool indent)

and pp_layout status =
 let pp_term = pp_term status in
 function
  | Ast.Sub (t1, t2) -> sprintf "%s \\SUB %s" (pp_term t1) (pp_term t2)
  | Ast.Sup (t1, t2) -> sprintf "%s \\SUP %s" (pp_term t1) (pp_term t2)
  | Ast.Below (t1, t2) -> sprintf "%s \\BELOW %s" (pp_term t1) (pp_term t2)
  | Ast.Above (t1, t2) -> sprintf "%s \\ABOVE %s" (pp_term t1) (pp_term t2)
  | Ast.Over (t1, t2) -> sprintf "[%s \\OVER %s]" (pp_term t1) (pp_term t2)
  | Ast.Atop (t1, t2) -> sprintf "[%s \\ATOP %s]" (pp_term t1) (pp_term t2)
  | Ast.Frac (t1, t2) -> sprintf "\\FRAC %s %s" (pp_term t1) (pp_term t2)
  | Ast.InfRule (t1, t2, t3) -> sprintf "\\INFRULE %s %s %s" (pp_term t1)
  (pp_term t2) (pp_term t3)
  | Ast.Maction l -> sprintf "\\MACTION (%s)" 
     (String.concat "," (List.map pp_term l))
  | Ast.Sqrt t -> sprintf "\\SQRT %s" (pp_term t)
  | Ast.Root (arg, index) ->
      sprintf "\\ROOT %s \\OF %s" (pp_term index) (pp_term arg)
  | Ast.Break -> "\\BREAK"
(*   | Space -> "\\SPACE" *)
  | Ast.Box (box_spec, terms) ->
      sprintf "\\%s [%s]" (pp_box_spec box_spec)
        (String.concat " " (List.map pp_term terms))
  | Ast.Group terms ->
      sprintf "\\GROUP [%s]" (String.concat " " (List.map pp_term terms))
  | Ast.Mstyle (l,terms) -> 
      sprintf "\\MSTYLE %s [%s]" 
        (String.concat " " (List.map (fun (k,v) -> k^"="^v) l))
        (String.concat " " (List.map pp_term terms))
  | Ast.Mpadded (l,terms) -> 
      sprintf "\\MSTYLE %s [%s]" 
        (String.concat " " (List.map (fun (k,v) -> k^"="^v) l))
        (String.concat " " (List.map pp_term terms))

and pp_magic status =
 let pp_term = pp_term status in
 function
  | Ast.List0 (t, sep_opt) ->
      sprintf "list0 %s%s" (pp_term t) (pp_sep_opt sep_opt)
  | Ast.List1 (t, sep_opt) ->
      sprintf "list1 %s%s" (pp_term t) (pp_sep_opt sep_opt)
  | Ast.Opt t -> sprintf "opt %s" (pp_term t)
  | Ast.Fold (kind, p_base, names, p_rec) ->
      let acc = match names with acc :: _ -> acc | _ -> assert false in
      sprintf "fold %s %s rec %s %s"
        (pp_fold_kind kind) (pp_term p_base) acc (pp_term p_rec)
  | Ast.Default (p_some, p_none) ->
      sprintf "default %s %s" (pp_term p_some) (pp_term p_none)
  | Ast.If (p_test, p_true, p_false) ->
      sprintf "if %s then %s else %s"
	(pp_term p_test) (pp_term p_true) (pp_term p_false)
  | Ast.Fail -> "fail"

and pp_fold_kind = function
  | `Left -> "left"
  | `Right -> "right"

and pp_sep_opt = function
  | None -> ""
  | Some sep -> sprintf " sep %s" (pp_literal sep)

and pp_variable = function
  | Ast.NumVar s -> "number " ^ s
  | Ast.IdentVar s -> "ident " ^ s
  | Ast.TermVar (s,Ast.Self _) -> s
  | Ast.TermVar (s,Ast.Level l) -> "term " ^string_of_int l 
  | Ast.Ascription (t, n) -> assert false
  | Ast.FreshVar n -> "fresh " ^ n

let _pp_term = ref (pp_term ~pp_parens:false)
let pp_term status t = !_pp_term (status :> NCic.status) t
let set_pp_term f = _pp_term := f

let pp_params pp_term = function
  | [] -> ""
  | params -> " " ^ String.concat " " (List.map (pp_capture_variable pp_term) params)
      
let pp_fields pp_term fields =
  (if fields <> [] then "\n" else "") ^ 
  String.concat ";\n" 
    (List.map 
      (fun (name,ty,coercion,arity) -> 
        " " ^ name ^ 
        (if coercion then 
	  (":" ^ (if arity > 0 then string_of_int arity else "") ^ "> ") 
	else ": ") ^
      pp_term ty)
    fields)

let string_of_source = function
   | `Provided  -> ""
   | `Implied   -> "implied "
   | `Generated -> "generated "

let pp_obj pp_term = function
 | Ast.Inductive (params, types, source) ->
    let pp_constructors constructors =
      String.concat "\n"
        (List.map (fun (name, typ) -> sprintf "| %s: %s" name (pp_term typ))
          constructors)
    in
    let pp_type (name, _, typ, constructors) =
      sprintf "\nwith %s: %s \\def\n%s" name (pp_term typ)
        (pp_constructors constructors)
    in
    (match types with
    | [] -> assert false
    | (name, inductive, typ, constructors) :: tl ->
        let fst_typ_pp =
          sprintf "%s%sinductive %s%s: %s \\def\n%s"
            (string_of_source source)
            (if inductive then "" else "co") name (pp_params pp_term params)
            (pp_term typ) (pp_constructors constructors)
        in
        fst_typ_pp ^ String.concat "" (List.map pp_type tl))
 | Ast.Theorem (name, typ, body,(source, flavour, _)) ->
    sprintf "%s%s %s:\n %s\n%s"
      (string_of_source source)
      (NCicPp.string_of_flavour flavour)
      name
      (pp_term typ)
      (match body with
      | None -> ""
      | Some body -> "\\def\n " ^ pp_term body)
 | Ast.Record (params,name,ty,fields, source) ->
    string_of_source source ^
    "record " ^ name ^ " " ^ pp_params pp_term params ^ ": " ^ pp_term ty ^ 
    " \\def {" ^ pp_fields pp_term fields ^ "\n}"
 | Ast.LetRec (kind, definitions, (source, flavour, _)) ->
    let rec get_guard i = function
       | []                   -> assert false (* Ast.Implicit `JustOne *)
       | [term, _] when i = 1 -> term
       | _ :: tl              -> get_guard (pred i) tl
    in
    let map (params, (id,typ), body, i) =
     let typ =
      match typ with
         None -> assert false (* Ast.Implicit `JustOne *)
       | Some typ -> typ
     in
       sprintf "%s %s on %s: %s \\def %s" 
	  (pp_term id)
	  (String.concat " " (List.map (pp_capture_variable pp_term) params))
	  (pp_term (get_guard i params))
	  (pp_term typ) (pp_term body)
    in
    sprintf "%s%s %s %s"
      (string_of_source source)
      (match kind with `Inductive -> "rec" | `CoInductive -> "corec")
      (NCicPp.string_of_flavour flavour)
      (String.concat " and " (List.map map definitions))

let rec pp_value (status: #NCic.status) = function
  | Env.TermValue t -> sprintf "$%s$" (pp_term status t)
  | Env.StringValue (Env.Ident s) -> sprintf "\"%s\"" s
  | Env.StringValue (Env.Var s) -> sprintf "\"${ident %s}\"" s
  | Env.NumValue n -> n
  | Env.OptValue (Some v) -> "Some " ^ pp_value status v
  | Env.OptValue None -> "None"
  | Env.ListValue l -> sprintf "[%s]" (String.concat "; " (List.map (pp_value status) l))

let rec pp_value_type =
  function
  | Env.TermType l -> "Term "^string_of_int l
  | Env.StringType -> "String"
  | Env.NumType -> "Number"
  | Env.OptType t -> "Maybe " ^ pp_value_type t
  | Env.ListType l -> "List " ^ pp_value_type l

let pp_env status env =
  String.concat "; "
    (List.map
      (fun (name, (ty, value)) ->
        sprintf "%s : %s = %s" name (pp_value_type ty) (pp_value status value))
      env)

let rec pp_cic_appl_pattern = function
  | Ast.NRefPattern nref -> NReference.string_of_reference nref
  | Ast.VarPattern name -> name
  | Ast.ImplicitPattern -> "?"
  | Ast.ApplPattern aps ->
      sprintf "(%s)" (String.concat " " (List.map pp_cic_appl_pattern aps))

