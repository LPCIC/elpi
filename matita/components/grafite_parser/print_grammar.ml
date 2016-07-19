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

(* $Id: print_grammar.ml 11672 2011-11-17 00:00:00Z sacerdot $ *)

open Gramext 

let rec flatten_tree = function
  | DeadEnd -> []
  | LocAct _ -> [[]]
  | Node {node = n; brother = b; son = s} ->
      List.map (fun l -> n :: l) (flatten_tree s) @ flatten_tree b

let tex_of_unicode s = s

let rec clean_dummy_desc = function
  | Dlevels l -> Dlevels (clean_levels l)
  | x -> x

and clean_levels = function
  | [] -> []
  | l :: tl -> clean_level l @ clean_levels tl
  
and clean_level = function
  | x -> 
      let pref = clean_tree x.lprefix in
      let suff = clean_tree x.lsuffix in
      match pref,suff with
      | DeadEnd, DeadEnd -> []
      | _ -> [{x with lprefix = pref; lsuffix = suff}]
  
and clean_tree = function
  | Node n -> clean_node n
  | x -> x
  
and clean_node = function
  | {node=node;son=son;brother=brother} ->
      let bn = is_symbol_dummy node in
      let bs = is_tree_dummy son in
      let bb = is_tree_dummy brother in
      let son = if bs then DeadEnd else son in
      let brother = if bb then DeadEnd else brother in
      if bb && bs && bn then
        DeadEnd
      else 
        if bn then 
          Node {node=Sself;son=son;brother=brother}
        else
          Node {node=node;son=son;brother=brother}

and is_level_dummy = function
  | {lsuffix=lsuffix;lprefix=lprefix} -> 
      is_tree_dummy lsuffix && is_tree_dummy lprefix
  
and is_desc_dummy = function
  | Dlevels l -> List.for_all is_level_dummy l
  | Dparser _ -> true
  
and is_entry_dummy = function
  | {edesc=edesc} -> is_desc_dummy edesc
  
and is_symbol_dummy = function
  | Stoken ("DUMMY", _) -> true
  | Stoken _ -> false
  | Smeta (_, lt, _) -> List.for_all is_symbol_dummy lt
  | Snterm e | Snterml (e, _) -> is_entry_dummy e
  | Slist1 x | Slist0 x -> is_symbol_dummy x
  | Slist1sep (x,y,false) | Slist0sep (x,y,false) -> is_symbol_dummy x && is_symbol_dummy y
  | Sopt x -> is_symbol_dummy x
  | Sself | Snext -> false
  | Stree t -> is_tree_dummy t
  | _ -> assert false
  
and is_tree_dummy = function
  | Node {node=node} -> is_symbol_dummy node 
  | _ -> true

let needs_brackets t =
  let rec count_brothers = function 
    | Node {brother = brother} -> 1 + count_brothers brother
    | _ -> 0
  in
  count_brothers t > 1

let visit_description desc fmt self = 
  let skip s = true in
  let inline s = List.mem s [ "int" ] in
  
  let rec visit_entry e ?level todo is_son  =
    let { ename = ename; edesc = desc } = e in 
    if inline ename then 
      visit_desc desc todo is_son 
    else
      begin
       (match level with
       | None -> Format.fprintf fmt "%s " ename;
       | Some _ -> Format.fprintf fmt "%s " ename;);
          if skip ename then
            todo
          else
            todo @ [e]
      end
      
  and visit_desc d todo is_son  =
    match d with
    | Dlevels l ->
        List.fold_left  
        (fun acc l -> 
           Format.fprintf fmt "@ ";
           visit_level l acc is_son ) 
          todo l;
    | Dparser _ -> todo
    
  and visit_level l todo is_son  =
    let { lname = name ; lsuffix = suff ; lprefix = pref } = l in
        visit_tree name
          (List.map 
            (fun x -> Sself :: x) (flatten_tree suff) @ flatten_tree pref)
          todo is_son  
    
  and visit_tree name t todo is_son  = 
    if List.for_all (List.for_all is_symbol_dummy) t then todo else (
    Format.fprintf fmt "@[<v>";
    (match name with 
    |Some name -> Format.fprintf fmt "Precedence %s:@ " name 
    | None -> ());
    Format.fprintf fmt "@[<v>";
    let todo = 
      List.fold_left 
       (fun acc x ->
         if List.for_all is_symbol_dummy x then todo else (
         Format.fprintf fmt "@[<h> | ";
         let todo = 
           List.fold_left 
            (fun acc x -> 
               let todo = visit_symbol x acc true in
               Format.fprintf fmt "@ ";
               todo)
            acc x
         in
         Format.fprintf fmt "@]@ ";
         todo))
       todo t 
    in
    Format.fprintf fmt "@]";
    Format.fprintf fmt "@]";
    todo)
    
  and visit_symbol s todo is_son  =
    match s with
    | Smeta (name, sl, _) -> 
        Format.fprintf fmt "%s " name;
        List.fold_left (
          fun acc s -> 
            let todo = visit_symbol s acc is_son  in
            if is_son then
              Format.fprintf fmt "@ ";
            todo) 
        todo sl
    | Snterm entry -> visit_entry entry todo is_son  
    | Snterml (entry,level) -> visit_entry entry ~level todo is_son 
    | Slist0 symbol -> 
        Format.fprintf fmt "{@[<hov2> ";
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "@]} @ ";
        todo
    | Slist0sep (symbol,sep,false) ->
        Format.fprintf fmt "[@[<hov2> ";
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "{@[<hov2> ";
        let todo = visit_symbol sep todo is_son in
        Format.fprintf fmt " ";
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "@]} @]] @ ";
        todo
    | Slist1 symbol -> 
        Format.fprintf fmt "{@[<hov2> ";
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "@]}+ @ ";
        todo 
    | Slist1sep (symbol,sep,false) ->
        let todo = visit_symbol symbol todo is_son  in
        Format.fprintf fmt "{@[<hov2> ";
        let todo = visit_symbol sep todo is_son in
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "@]} @ ";
        todo
    | Sopt symbol -> 
        Format.fprintf fmt "[@[<hov2> ";
        let todo = visit_symbol symbol todo is_son in
        Format.fprintf fmt "@]] @ ";
        todo
    | Sself -> Format.fprintf fmt "%s " self; todo
    | Snext -> Format.fprintf fmt "next "; todo
    | Stoken pattern -> 
        let constructor, keyword = pattern in
        if keyword = "" then
          (if constructor <> "DUMMY" then
            Format.fprintf fmt "`%s' " constructor)
        else
          Format.fprintf fmt "%s " (tex_of_unicode keyword);
        todo
    | Stree tree ->
        visit_tree None (flatten_tree tree) todo is_son 
    | _ -> assert false
  in
  visit_desc desc [] false
;;


let rec visit_entries fmt todo pped =
  match todo with
  | [] -> ()
  | hd :: tl -> 
      let todo =
        if not (List.memq hd pped) then
          begin
            let { ename = ename; edesc = desc } = hd in 
            Format.fprintf fmt "@[<hv 2>%s ::= " ename;
            let desc = clean_dummy_desc desc in 
            let todo = visit_description desc fmt ename @ todo in
            Format.fprintf fmt "@]\n\n";
            todo 
          end
        else
          todo
      in
      let clean_todo todo =
        let name_of_entry e = e.ename in
        let pped = hd :: pped in
        let todo = tl @ todo in
        let todo = List.filter (fun e -> not(List.memq e pped)) todo in
        HExtlib.list_uniq 
          ~eq:(fun e1 e2 -> (name_of_entry e1) = (name_of_entry e2))
          (List.sort 
            (fun e1 e2 -> 
              Pervasives.compare (name_of_entry e1) (name_of_entry e2))
            todo),
        pped
      in
      let todo,pped = clean_todo todo in
      visit_entries fmt todo pped
;;

let ebnf_of_term status =
  let g_entry = Grammar.Entry.obj (CicNotationParser.term status) in
  let buff = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer buff in
  visit_entries fmt [g_entry] [];
  Format.fprintf fmt "@?";
  let s = Buffer.contents buff in
  s
;;
