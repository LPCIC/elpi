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

(* $Id: nCicPp.ml 13076 2015-09-05 15:14:26Z fguidi $ *)

module C = NCic
module R = NReference
module F = Format

let r2s status pp_fix_name r = 
  try
    match r with
    | R.Ref (u,R.Ind (_,i,_)) -> 
        (match NCicEnvironment.get_checked_obj status u with
        | _,_,_,_, C.Inductive (_,_,itl,_) ->
            let _,name,_,_ = List.nth itl i in name
        | _ -> assert false)
    | R.Ref (u,R.Con (i,j,_)) -> 
        (match NCicEnvironment.get_checked_obj status u with
        | _,_,_,_, C.Inductive (_,_,itl,_) ->
            let _,_,_,cl = List.nth itl i in
            let _,name,_ = List.nth cl (j-1) in name
        | _ -> assert false)
    | R.Ref (u,(R.Decl | R.Def _)) -> 
        (match NCicEnvironment.get_checked_obj status u with
        | _,_,_,_, C.Constant (_,name,_,_,_) -> name
        | _ -> assert false)
    | R.Ref (u,(R.Fix (i,_,_)|R.CoFix i)) ->
        (match NCicEnvironment.get_checked_obj status u with
        | _,_,_,_, C.Fixpoint (_,fl,_) -> 
            if pp_fix_name then
              let _,name,_,_,_ = List.nth fl i in name
            else 
              NUri.name_of_uri u (*^"("^ string_of_int i ^ ")"*)
        | _ -> assert false)
  with 
  | NCicEnvironment.ObjectNotFound _ 
  | Failure "nth" 
  | Invalid_argument "List.nth" -> R.string_of_reference r
;;

let string_of_implicit_annotation = function
  | `Closed -> "▪"
  | `Type -> ""
  | `Hole -> "□"
  | `Tagged s -> "[\"" ^ s ^ "\"]"
  | `Term -> "Term"
  | `Typeof x -> "Ty("^string_of_int x^")"
  | `Vector -> "…"
;;

let ppterm status ~formatter:f ~context ~subst ~metasenv:_ ?(inside_fix=false) t =
 let rec aux ?(toplevel=false) ctx = function
  | C.Rel m ->
        (try 
           let name = List.nth ctx (m-1) in
           F.fprintf f "%s" (if name = "_" then "__"^string_of_int m else name)
        with Failure "nth" | Invalid_argument "List.nth" -> 
            F.fprintf f " -%d" (m - List.length ctx))
  | C.Const r -> F.fprintf f "%s" (r2s status inside_fix r)
  | C.Prod ("_",s,t) -> 
      if not toplevel then F.fprintf f "(";
      F.fprintf f "@[<hov 1>";
      (match s with 
      | C.Prod ("_",_,_) -> aux ~toplevel:false ctx s 
      | _ -> aux ~toplevel:true ctx s);
      F.fprintf f "@;→ ";
      aux ~toplevel:true ("_"::ctx) t;
      F.fprintf f "@]";
      if not toplevel then F.fprintf f ")";
  | C.Prod (name,s,t) -> 
      if not toplevel then F.fprintf f "(";
      F.fprintf f "@[<hov 1>";
      F.fprintf f "@[<hov 2>∀%s:@;" name;
      aux ~toplevel:true ctx s; 
      F.fprintf f "@].@;";
      aux ~toplevel:true (name::ctx) t;
      F.fprintf f "@]";
      if not toplevel then F.fprintf f ")";
  | C.Lambda (name,s,t) -> 
      if not toplevel then F.fprintf f "(";
      F.fprintf f "@[<hov 1>";
      F.fprintf f "λ%s:" name;
      aux ~toplevel:true ctx s; 
      F.fprintf f ".@;";
      aux ~toplevel:true (name::ctx) t;
      F.fprintf f "@]";
      if not toplevel then F.fprintf f ")";
  | C.LetIn (name,ty,t,b) -> 
      if not toplevel then F.fprintf f "(";
      F.fprintf f "@[<hov 1>";
      F.fprintf f "let %s:@;" name;
      aux ~toplevel:true ctx ty;
      F.fprintf f "@;≝ ";
      aux ~toplevel:true ctx t;
      F.fprintf f "@;in@;";
      (aux ~toplevel:true (name::ctx) b);
      F.fprintf f "@]";
      if not toplevel then F.fprintf f ")";
  | C.Match (r,oty,t,pl) ->
      F.fprintf f "@[<hov>match ";
      aux ~toplevel:true ctx t;
      F.fprintf f "@;return ";
      aux ~toplevel:true ctx oty;
      F.fprintf f "@; @[<v>[ ";
      if pl <> [] then
        begin
          F.fprintf f "@[<hov 2>%s ⇒@;" 
            (try r2s status inside_fix (R.mk_constructor 1 r)
             with R.IllFormedReference _ -> "#ERROR#");
          aux ~toplevel:true ctx (List.hd pl);
          F.fprintf f "@]";
          ignore(List.fold_left 
            (fun i t -> 
             F.fprintf f "@;| @[<hov 2>%s ⇒@;" 
               (try r2s status inside_fix (R.mk_constructor i r)
                with R.IllFormedReference _ -> "#ERROR#");
             aux ~toplevel:true ctx t; 
             F.fprintf f "@]";
             i+1)
            2 (List.tl pl));
        end;
     F.fprintf f "]@] @]";
  | C.Appl [] -> 
      F.fprintf f "BAD APPLICATION: empty list"
  | C.Appl [x] ->
      F.fprintf f "BAD APPLICATION: just the head: ";
      aux ctx x
  | C.Appl (C.Appl _ as x::_) -> 
      F.fprintf f "BAD APPLICATION: appl of appl with head: ";
      aux ctx x
  | C.Appl (C.Meta (n,lc) :: args) when List.mem_assoc n subst -> 
      let _,_,t,_ = List.assoc n subst in
      let hd = NCicSubstitution.subst_meta status lc t in
      aux ctx 
        (NCicReduction.head_beta_reduce (status :> NCic.status) ~upto:(List.length args)
          (match hd with
          | NCic.Appl l -> NCic.Appl (l@args)
          | _ -> NCic.Appl (hd :: args)))
  | C.Appl l -> 
      F.fprintf f "@[<hov 2>";
      if not toplevel then F.fprintf f "(";
      aux ctx (List.hd l);
      List.iter (fun x -> F.fprintf f "@;";aux ctx x) (List.tl l);
      if not toplevel then F.fprintf f ")";
      F.fprintf f "@]"
  | C.Implicit annot -> 
      F.fprintf f "?%s" (string_of_implicit_annotation annot)
  | C.Meta (n,lc) when List.mem_assoc n subst -> 
       let _,_,t,_ = List.assoc n subst in
       aux ctx (NCicSubstitution.subst_meta status lc t)
  | C.Meta (n,(shift,C.Irl len)) -> 
       F.fprintf f "?%d(%d,%d)" n shift len
  | C.Meta (n,(shift,C.Ctx l)) -> 
       F.fprintf f "?%d(%d,[" n shift;
       if List.length l > 0 then
         begin 
           aux ctx (NCicSubstitution.lift status shift (List.hd l));
           List.iter (fun x -> F.fprintf f ",";aux ctx x) 
            (List.map (NCicSubstitution.lift status shift) (List.tl l));
         end;
       F.fprintf f "])"
  | C.Sort s -> NCicEnvironment.ppsort f s
 in 
  aux ~toplevel:true (List.map fst context) t
;;

let on_buffer f t = 
 try
  let buff = Buffer.create 100 in
  let formatter = F.formatter_of_buffer buff in
  f ~formatter:formatter t;
  F.fprintf formatter "@?";
  Buffer.contents buff
 with Failure m ->
  "[[Unprintable: " ^ m ^ "]]"
;;

let ppterm ~formatter ~context ~subst ~metasenv ?(margin=80) ?inside_fix t = 
  F.set_margin margin;
  ppterm ~formatter ~context ~subst ~metasenv ?inside_fix t
;;

let rec ppcontext status ~formatter ?(sep="; ") ~subst ~metasenv = function
  | [] -> ()
  | (name, NCic.Decl t) :: tl -> 
      ppcontext status ~formatter ~sep ~subst ~metasenv tl;
      F.fprintf formatter "%s: " name;
      ppterm status ~formatter ~subst ~metasenv ~context:tl t;
      F.fprintf formatter "%s@;" sep
  | (name, NCic.Def (bo,ty)) :: tl->
      ppcontext status ~formatter ~sep ~subst ~metasenv tl;
      F.fprintf formatter "%s: " name;
      ppterm status ~formatter ~subst ~metasenv ~context:tl ty;
      F.fprintf formatter " := ";
      ppterm status ~formatter ~subst ~metasenv ~context:tl bo;
      F.fprintf formatter "%s@;" sep
;;
let ppcontext status ~formatter ?sep ~subst ~metasenv c =
  F.fprintf formatter "@[<hov>";
  ppcontext status ~formatter ?sep ~subst ~metasenv c;
  F.fprintf formatter "@]";
;;

let ppmetaattrs =
 function
    [] -> ""
  | attrs ->
   "(" ^
    String.concat ","
     (List.map
       (function
         | `IsTerm -> "term"
         | `IsType -> "type"
         | `IsSort -> "sort"
         | `Name n -> "name=" ^ n
         | `InScope -> "in_scope"
         | `OutScope n -> "out_scope:" ^ string_of_int n
       ) attrs) ^
    ")"
;;

let rec ppmetasenv status ~formatter ~subst metasenv = function
  | [] -> ()
  | (i,(attrs, ctx, ty)) :: tl ->
      F.fprintf formatter "@[<hov 2>";
      ppcontext status ~formatter ~sep:"; " ~subst ~metasenv ctx;
      F.fprintf formatter "@;⊢@;?%d%s :@;" i (ppmetaattrs attrs);
      ppterm status ~formatter ~metasenv ~subst ~context:ctx ty;
      F.fprintf formatter "@]@\n";
      ppmetasenv status ~formatter ~subst metasenv tl
;;

let ppmetasenv status ~formatter ~subst metasenv =
 ppmetasenv status ~formatter ~subst metasenv metasenv
;;

let rec ppsubst status ~formatter ~subst ~metasenv = function
  | [] -> ()
  | (i,(attrs, ctx, t, ty)) :: tl ->
      ppcontext status ~formatter ~sep:"; " ~subst ~metasenv ctx;
      F.fprintf formatter " ⊢ ?%d%s := " i (ppmetaattrs attrs);
      ppterm status ~formatter ~metasenv ~subst ~context:ctx t;
      F.fprintf formatter " : ";
      ppterm status ~formatter ~metasenv ~subst ~context:ctx ty;
      F.fprintf formatter "\n";
      ppsubst status ~formatter ~subst ~metasenv tl
;;

let ppsubst status ~formatter ~metasenv ?(use_subst=true) subst =
 let ssubst = if use_subst then subst else [] in
  ppsubst status ~formatter ~metasenv ~subst:ssubst subst
;;

let string_of_generated = function
  | `Generated -> "Generated"
  | `Provided -> "Provided"
  | `Implied -> "Implied"
;;

let string_of_flavour = function
  | `Axiom -> "axiom"
  | `Definition -> "definition"
  | `Fact -> "fact"
  | `Lemma -> "lemma"
  | `Theorem -> "theorem"
  | `Corollary -> "corollary"
  | `Example -> "example"
;;
        
let string_of_pragma = function
  | `Coercion _arity -> "Coercion _"
  | `Elim _sort -> "Elim _"
  | `Projection -> "Projection"
  | `InversionPrinciple -> "InversionPrinciple"
  | `DiscriminationPrinciple -> "DiscriminationPrinciple"
  | `Variant -> "Variant"
  | `Local -> "Local"
  | `Regular -> "Regular"
;;

let string_of_fattrs (g,f,p) = 
  String.concat ","
   [ string_of_generated g; string_of_flavour f; string_of_pragma p ]
;;

let ppobj status ~formatter (u,_,metasenv, subst, o) = 
  F.fprintf formatter "metasenv:\n";
  ppmetasenv status ~formatter ~subst metasenv;
  F.fprintf formatter "\n";
  F.fprintf formatter "subst:\n";
  (*ppsubst subst ~formatter ~metasenv;*) F.fprintf formatter "...";
  F.fprintf formatter "\n";
  match o with 
  | NCic.Fixpoint (b, fl, attrs) -> 
      F.fprintf formatter "{%s}@\n@[<hov 0>" (NUri.string_of_uri u);
      F.fprintf formatter "@[<hov 2>%s"(if b then "let rec " else "let corec ");
      HExtlib.list_iter_sep
       ~sep:(fun () -> F.fprintf formatter "@\n@[<hov 2>and ")
       (fun (_,name,n,ty,bo) ->
        F.fprintf formatter "%s on %d :@;" name n;
        ppterm status ~formatter ~metasenv ~subst ~context:[] ty;
        F.fprintf formatter "@]@;@[<hov 2>:=@;";
        ppterm status ~formatter ~metasenv ~subst ~context:[] ~inside_fix:true bo;
        F.fprintf formatter "@]") fl;
      F.fprintf formatter "@; %s" (string_of_fattrs attrs);
      F.fprintf formatter "@]"
  | NCic.Inductive (b, leftno,tyl, _) -> 
      F.fprintf formatter "{%s} with %d fixed params@\n@[<hov 0>@[<hov 2>%s"
       (NUri.string_of_uri u) leftno
       (if b then "inductive " else "coinductive ");
      HExtlib.list_iter_sep
        ~sep:(fun () -> F.fprintf formatter "@\n@[<hov 2>and ")
       (fun (_,name,ty,cl) ->
          F.fprintf formatter "%s:@;" name;
          ppterm status ~formatter ~metasenv ~subst ~context:[] ty;
          F.fprintf formatter "@]@;@[<hov 3>:=@;";
          HExtlib.list_iter_sep ~sep:(fun () -> F.fprintf formatter "@;")
           (fun (_,name,ty) ->
             F.fprintf formatter "| %s: " name;
             ppterm status ~formatter ~metasenv ~subst ~context:[] ty;)
           cl;
          F.fprintf formatter "@]"
        ) tyl ;
        F.fprintf formatter "@]"
  | NCic.Constant (_,name,None,ty, _) -> 
     F.fprintf formatter "{%s}@\n@[<hov 2>axiom %s :@;" (NUri.string_of_uri u) name;
     ppterm status ~formatter ~metasenv ~subst ~context:[] ty;
     F.fprintf formatter "@]@\n"
  | NCic.Constant (_,name,Some bo,ty, _) ->
     F.fprintf formatter "{%s}@\n@[<hov 0>@[<hov 2>definition %s :@;" (NUri.string_of_uri u) name;
     ppterm status ~formatter ~metasenv ~subst ~context:[] ty;
     F.fprintf formatter "@]@;@[<hov 2>:=@;";
     ppterm status ~formatter ~metasenv ~subst ~context:[] bo;
     F.fprintf formatter "@]@\n@]"
;;

let ppterm status ~context ~subst ~metasenv ?margin ?inside_fix t = 
 on_buffer (ppterm status ~context ~subst ~metasenv ?margin ?inside_fix) t
;;

let ppcontext status ?sep ~subst ~metasenv ctx =
 on_buffer (ppcontext status ?sep ~subst ~metasenv) ctx
;;

let ppmetasenv status ~subst metasenv =
 on_buffer (ppmetasenv status ~subst) metasenv
;;

let ppsubst status ~metasenv ?use_subst subst =
 on_buffer (ppsubst status ~metasenv ?use_subst) subst
;;

let ppobj status obj = on_buffer (ppobj status) obj;;

class status =
 object(self)
  (* this method is meant to be overridden in ApplyTransformation *)
  method ppterm = ppterm self
  method ppcontext = ppcontext self
  method ppmetasenv = ppmetasenv self
  method ppsubst = ppsubst self
  method ppobj = ppobj self
 end
