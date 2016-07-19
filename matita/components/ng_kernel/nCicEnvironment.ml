(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCicEnvironment.ml 13176 2016-04-18 15:29:33Z fguidi $ *)

module C = NCic
module Ref = NReference

exception CircularDependency of string Lazy.t;;
exception ObjectNotFound of string Lazy.t;;
exception BadDependency of string Lazy.t * exn;;
exception BadConstraint of string Lazy.t;;
exception AlreadyDefined of string Lazy.t;;

let cache = NUri.UriHash.create 313;;
let history = ref [];;
let frozen_list = ref [];;

let get_obj = ref (fun _ _ -> assert false);;
let set_get_obj = (:=) get_obj;;

module F = Format 

let rec ppsort f = function
  | C.Prop -> F.fprintf f "Prop"
  | (C.Type []) -> F.fprintf f "Type0"
  | (C.Type [`Type, u]) -> F.fprintf f "%s" (NUri.name_of_uri u)
  | (C.Type [`Succ, u]) -> F.fprintf f "S(%s)" (NUri.name_of_uri u)
  | (C.Type [`CProp, u]) -> F.fprintf f "P(%s)" (NUri.name_of_uri u)
  | (C.Type l) -> 
      F.fprintf f "Max(";
      ppsort f ((C.Type [List.hd l]));
      List.iter (fun x -> F.fprintf f ",";ppsort f ((C.Type [x]))) (List.tl l);
      F.fprintf f ")"
;;

let string_of_univ u =
  let b = Buffer.create 100 in
  let f = Format.formatter_of_buffer b in
  ppsort f (NCic.Type u);
  Format.fprintf f "@?";
  Buffer.contents b
;;

let eq_univ (b1,u1) (b2,u2) = b1=b2 && NUri.eq u1 u2;;

let max (l1:NCic.universe) (l2:NCic.universe) =
 match l2 with
 | x::tl -> 
    let rest = List.filter (fun y -> not (eq_univ x y)) (l1@tl) in
    x :: HExtlib.list_uniq ~eq:eq_univ
      (List.sort (fun (b1,u1) (b2,u2) ->
         let res = compare b1 b2 in 
         if res = 0 then NUri.compare u1 u2 else res)
      rest)
 | [] -> 
     match l1 with
     | [] -> []
     | ((`Type|`Succ), _)::_ -> l1
     | (`CProp, u)::tl -> (`Type, u)::tl
;;

let lt_constraints = ref [] (* a,b := a < b *)

let rec lt_path_uri avoid a b = 
 List.exists
  (fun (x,y) ->
      NUri.eq y b && 
     (NUri.eq a x ||
        (not (List.exists (NUri.eq x) avoid) &&
        lt_path_uri (x::avoid) a x))
  ) !lt_constraints
;;

let lt_path a b = lt_path_uri [b] a b;;

let universe_eq a b = 
  match a,b with 
  | [(`Type|`CProp) as b1, u1], [(`Type|`CProp) as b2, u2] -> 
         b1 = b2 && NUri.eq u1 u2
  | _, [(`Type|`CProp),_]
  | [(`Type|`CProp),_],_ -> false
  | _ ->
     raise (BadConstraint
      (lazy "trying to check if two inferred universes are equal"))
;;

let universe_leq a b = 
  match a, b with
  | (((`Type|`Succ),_)::_ | []) , [`CProp,_] -> false
  | l, [((`Type|`CProp),b)] -> 
       List.for_all 
         (function 
         | `Succ,a -> lt_path a b 
         | _, a -> NUri.eq a b || lt_path a b) l
  | _, ([] | [`Succ,_] | _::_::_) -> 
     raise (BadConstraint (lazy (
       "trying to check if "^string_of_univ a^
       " is leq than the inferred universe " ^ string_of_univ b)))
;;

let are_sorts_convertible ~test_eq_only s1 s2 =
   match s1,s2 with
   | C.Type a, C.Type b when not test_eq_only -> universe_leq a b
   | C.Type a, C.Type b -> universe_eq a b
   | C.Prop,C.Type _ -> (not test_eq_only)
   | C.Prop, C.Prop -> true
   | _ -> false
;;

let pp_constraint x y =  
  NUri.name_of_uri x ^ " < " ^ NUri.name_of_uri y
;;

let pp_constraints () =
  String.concat "\n" (List.map (fun (x,y) -> pp_constraint x y) !lt_constraints)
;;

let universes = ref [];;

let get_universes () = 
  List.map (fun x -> [`Type,x]) !universes @
  List.map (fun x -> [`CProp,x]) !universes
;;

let is_declared u =
 match u with
 | [(`CProp|`Type),x] -> List.exists (fun y -> NUri.eq x y) !universes
 | _ -> assert false
;;

exception UntypableSort of string Lazy.t
exception AssertFailure of string Lazy.t

let typeof_sort = function
  | C.Type ([(`Type|`CProp),u] as univ) ->
     if is_declared univ then (C.Type [`Succ, u])
     else 
      let universes = !universes in
       raise (UntypableSort (lazy ("undeclared universe " ^
         NUri.string_of_uri u ^ "\ndeclared ones are: " ^ 
         String.concat ", " (List.map NUri.string_of_uri universes)
     )))
  | C.Type t -> 
      raise (AssertFailure (lazy (
              "Cannot type an inferred type: "^ string_of_univ t)))
  | C.Prop -> (C.Type [])
;;

let add_lt_constraint ~acyclic a b = 
  match a,b with
  | [`Type,a2],[`Type,b2] -> 
      if not (lt_path_uri [] a2 b2) then (
        if acyclic && (lt_path_uri [] b2 a2 || NUri.eq a2 b2) then
         (raise(BadConstraint(lazy("universe inconsistency adding "^
                    pp_constraint a2 b2
           ^ " to:\n" ^ pp_constraints ()))));
        universes := a2 :: b2 :: 
          List.filter (fun x -> not (NUri.eq x a2 || NUri.eq x b2)) !universes;
        lt_constraints := (a2,b2) :: !lt_constraints);
      history := (`Constr (a,b))::!history;
  | _ -> raise (BadConstraint
          (lazy "trying to add a constraint on an inferred universe"))
;;
   
let family_of = function (`CProp,_)::_ -> `CProp | _ -> `Type ;;

let sup fam l =
  match l with
  | [(`Type|`CProp),_] -> Some l
  | l ->
   let bigger_than acc (s1,n1) = 
    List.filter
     (fun x -> lt_path_uri [] n1 x || (s1 <> `Succ && NUri.eq n1 x)) acc 
   in
   let solutions = List.fold_left bigger_than !universes l in
   let rec aux = function
     | [] -> None
     | u :: tl ->
         if List.exists (fun x -> lt_path_uri [] x u) solutions then aux tl
         else Some [fam,u]
   in
    aux solutions
;;

let sup l = sup (family_of l) l;;

let inf ~strict fam l =
  match l with
  | [(`Type|`CProp),_] -> Some l
  | [] -> None
  | l ->
   let smaller_than acc (_s1,n1) = 
    List.filter
     (fun x -> lt_path_uri [] x n1 || (not strict && NUri.eq n1 x)) acc 
   in
   let solutions = List.fold_left smaller_than !universes l in
   let rec aux = function
     | [] -> None
     | u :: tl ->
         if List.exists (lt_path_uri [] u) solutions then aux tl
         else Some [fam,u]
   in
    aux solutions
;;

let inf ~strict l = inf ~strict (family_of l) l;;

let rec universe_lt a b = 
  match a, b with
  | (((`Type|`Succ),_)::_ | []) , [`CProp,_] -> false
  | l, ([((`Type|`CProp),b)] as orig_b) -> 
       List.for_all 
         (function 
         | `Succ,_ as a -> 
             (match sup [a] with
             | None -> false
             | Some x -> universe_lt x orig_b) 
         | _, a -> lt_path a b) l
  | _, ([] | [`Succ,_] | _::_::_) -> 
     raise (BadConstraint (lazy (
       "trying to check if "^string_of_univ a^
       " is lt than the inferred universe " ^ string_of_univ b)))
;;


let allowed_sort_elimination s1 s2 =
  match s1, s2 with
  | C.Type (((`Type|`Succ),_)::_ | []), C.Type (((`Type|`Succ),_)::_ | []) 
  | C.Type _, C.Type ((`CProp,_)::_) 
  | C.Type _, C.Prop
  | C.Prop, C.Prop -> `Yes

  | C.Type ((`CProp,_)::_), C.Type (((`Type|`Succ),_)::_ | [])
  | C.Prop, C.Type _ -> `UnitOnly
;;

let typecheck_obj,already_set = ref (fun _ _ -> assert false), ref false;;
let set_typecheck_obj f =
 if !already_set then
  assert false
 else
  begin
   typecheck_obj := f;
   already_set := true
  end
;;

(* CSC: old code that performs recursive invalidation; to be removed
 * once we understand what we really want. Once we removed it, we can
 * also remove the !history
let invalidate_item item =
 let item_eq a b = 
   match a, b with
   | `Obj (u1,_), `Obj (u2,_) -> NUri.eq u1 u2
   | `Constr _, `Constr _ -> a=b (* MAKE EFFICIENT *)
   | _ -> false
 in
 let rec aux to_be_deleted =
  function
     [] -> assert false
   | item'::tl when item_eq item item' -> item'::to_be_deleted,tl
   | item'::tl -> aux (item'::to_be_deleted) tl
 in
  let to_be_deleted,h = aux [] !history in
   history := h;
   List.iter 
     (function 
     | `Obj (uri,_) -> NUri.UriHash.remove cache uri
     | `Constr ([_,u1],[_,u2]) as c -> 
          let w = u1,u2 in
          if not(List.mem c !history) then 
           lt_constraints := List.filter ((<>) w) !lt_constraints;
     | `Constr _ -> assert false
     ) to_be_deleted
;;
*)

let invalidate_item =
 function
    `Obj (uri,_) -> NUri.UriHash.remove cache uri
  | `Constr ([_,u1],[_,u2]) -> 
      let w = u1,u2 in
      lt_constraints := List.filter ((<>) w) !lt_constraints;
  | `Constr _ -> assert false
;;

exception Propagate of NUri.uri * exn;;

let to_exn f x =
 match f x with
    `WellTyped o -> o
  | `Exn e -> raise e
;;

let check_and_add_obj (status:#NCic.status) ((u,_,_,_,_) as obj) =
 let saved_frozen_list = !frozen_list in
 try
   frozen_list := (u,obj)::saved_frozen_list;
   HLog.warn ("Typechecking of " ^ NUri.string_of_uri u); 
   !typecheck_obj (status :> NCic.status) obj;
   frozen_list := saved_frozen_list;
   let obj' = `WellTyped obj in
   NUri.UriHash.add cache u obj';
   history := (`Obj (u,obj))::!history;
   obj'
 with
    Sys.Break as e ->
     frozen_list := saved_frozen_list;
     raise e
  | Propagate (u',old_exn) as e' ->
     frozen_list := saved_frozen_list;
     let exn = `Exn (BadDependency (lazy (NUri.string_of_uri u ^
       " depends (recursively) on " ^ NUri.string_of_uri u' ^
       " which is not well-typed"), 
       match old_exn with BadDependency (_,e) -> e | _ -> old_exn)) in
     NUri.UriHash.add cache u exn;
     history := (`Obj (u,obj))::!history;
     if saved_frozen_list = [] then
      exn
     else
      raise e'
  | e ->
     frozen_list := saved_frozen_list;
     let exn = `Exn e in
     history := (`Obj (u,obj))::!history;
     if saved_frozen_list = [] then
      exn
     else
      begin
       NUri.UriHash.add cache u exn;
       raise (Propagate (u,e))
      end
;;

let get_checked_obj status u =
 if List.exists (fun (k,_) -> NUri.eq u k) !frozen_list
 then
  raise (CircularDependency (lazy (NUri.string_of_uri u)))
 else
  try NUri.UriHash.find cache u
  with Not_found -> check_and_add_obj status (!get_obj (status :> NCic.status) u)
;;

let get_checked_obj (status:#NCic.status) u = to_exn (get_checked_obj status) u;;

let check_and_add_obj status ((u,_,_,_,_) as obj) =
 if NUri.UriHash.mem cache u then
  raise (AlreadyDefined (lazy (NUri.string_of_uri u)))
 else
  ignore (to_exn (check_and_add_obj status) obj)
;;

let get_checked_decl status = function
  | Ref.Ref (uri, Ref.Decl) ->
      (match get_checked_obj status uri with
      | _,height,_,_, C.Constant (rlv,name,None,ty,att) ->
          rlv,name,ty,att,height
      | _,_,_,_, C.Constant (_,_,Some _,_,_) ->
          prerr_endline "get_checked_decl on a definition"; assert false
      | _ -> prerr_endline "get_checked_decl on a non decl 2"; assert false)
  | _ -> prerr_endline "get_checked_decl on a non decl"; assert false
;;

let get_checked_def status = function
  | Ref.Ref (uri, Ref.Def _) ->
      (match get_checked_obj status uri with
      | _,height,_,_, C.Constant (rlv,name,Some bo,ty,att) ->
          rlv,name,bo,ty,att,height
      | _,_,_,_, C.Constant (_,_,None,_,_) ->
          prerr_endline "get_checked_def on an axiom"; assert false
      | _ -> prerr_endline "get_checked_def on a non def 2"; assert false)
  | _ -> prerr_endline "get_checked_def on a non def"; assert false
;;

let get_checked_indtys status = function
  | Ref.Ref (uri, (Ref.Ind (_,n,_)|Ref.Con (n,_,_))) ->
      (match get_checked_obj status uri with
      | _,_,_,_, C.Inductive (inductive,leftno,tys,att) ->
        inductive,leftno,tys,att,n
      | _ -> prerr_endline "get_checked_indtys on a non ind 2"; assert false)
  | _ -> prerr_endline "get_checked_indtys on a non ind"; assert false
;;

let get_checked_fixes_or_cofixes status = function
  | Ref.Ref (uri, (Ref.Fix _|Ref.CoFix _))->
      (match get_checked_obj status uri with
      | _,height,_,_, C.Fixpoint (_,funcs,att) ->
         funcs, att, height
      | _ ->prerr_endline "get_checked_(co)fix on a non (co)fix 2";assert false)
  | _ -> prerr_endline "get_checked_(co)fix on a non (co)fix"; assert false
;;

let get_relevance status (Ref.Ref (_, infos) as r) =
  match infos with
     Ref.Def _ -> let res,_,_,_,_,_ = get_checked_def status r in res
   | Ref.Decl -> let res,_,_,_,_ = get_checked_decl status r in res
   | Ref.Ind _ ->
       let _,_,tl,_,n = get_checked_indtys status r in
       let res,_,_,_ = List.nth tl n in
         res
    | Ref.Con (_,i,_) ->
       let _,_,tl,_,n = get_checked_indtys status r in
       let _,_,_,cl = List.nth tl n in
       let res,_,_ = List.nth cl (i - 1) in
         res
    | Ref.Fix (fixno,_,_)
    | Ref.CoFix fixno ->
        let fl,_,_ = get_checked_fixes_or_cofixes status r in
        let res,_,_,_,_ = List.nth fl fixno in
          res
;;


let invalidate _ = 
  assert (!frozen_list = []);
  NUri.UriHash.clear cache
;;
