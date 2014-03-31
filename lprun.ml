open Lpdata

module Subst = struct (* {{{ *)

type subst = { assign : LP.data Int.Map.t; top_uv : int }
let empty n = { assign = Int.Map.empty; top_uv = n }

let last_sub_lookup = ref (LP.DB 0)
let in_sub i { assign = assign } =
  try last_sub_lookup := Int.Map.find i assign; true
  with Not_found -> false
let set_sub i t s = { s with assign = Int.Map.add i t s.assign }

let rec iter_sep spc pp = function
  | [] -> ()
  | [x] -> pp x
  | x::tl -> pp x; spc (); iter_sep spc pp tl

let print_substf fmt s =
  Format.pp_open_hovbox fmt 2;
  Format.pp_print_string fmt "{ ";
  iter_sep
    (fun () -> Format.pp_print_string fmt ";";Format.pp_print_space fmt ())
    (fun (i,t) ->
       Format.pp_open_hvbox fmt 0;
       Format.pp_print_string fmt (LP.pr_var i);
       Format.pp_print_space fmt ();
       Format.pp_print_string fmt ":= ";
       LP.printf [] fmt t;
       Format.pp_close_box fmt ())
    (Int.Map.bindings s.assign);
  Format.pp_print_string fmt " }";
  Format.pp_close_box fmt ()
let print_subst s = on_buffer print_substf s

let apply_subst s t =
  let rec subst = function
    | LP.Uv(i,_,_) when in_sub i s -> LP.map subst !last_sub_lookup
    | x -> x in
  LP.map subst t
let apply_subst_goal s = function
  | LP.Atom t -> LP.Atom(apply_subst s t)
  | _ -> assert false

let refresh_uv depth s x =
  LP.map (function LP.Uv(i,_,a) -> LP.Uv(s.top_uv + i,depth,a) | x -> x) x

let top s = s.top_uv
let set_top i s = { s with top_uv = s.top_uv + i + 1 }

let fresh_uv lvl a s = LP.Uv(s.top_uv,lvl,a), { s with top_uv = s.top_uv + 1 }

end (* }}} *)

open Subst

module Red = struct (* {{{ *)

open LP

let rec lift n k = function
  | Uv _ as x -> x
  | Con _ as x -> x
  | DB m when m > n -> DB (m+k)
  | DB _ as x -> x
  | Bin (ns,t) as x ->
      let t' = lift (n+ns) k t in
      if t == t' then x else Bin(ns,t')
  | Tup xs as x ->
      let xs' = IA.map (lift n k) xs in
      if xs' == xs then x else Tup xs'
  | Ext _ as x -> x
let lift ?(from=0) k t = if k = 0 then t else lift from k t

(* DB i := v.(start + len - i) *)
let rec beta depth t start len v =
  match t with
  | (Con _ | Ext _ | Uv _) as x -> x
  | DB m when m > depth && m - depth <= len ->
      lift depth (IA.get (start + len - (m - depth)) v)
  | DB m when m > depth -> DB (m - len)
  | DB _ as x -> x
  | Tup xs -> Tup(IA.map (fun t -> beta depth t start len v) xs)
  | Bin(ns,b) -> Bin(ns,beta (depth+ns) b start len v)

let rec whd s t =
  match t with
  | (Ext _ | Con _ | DB _ | Bin _) as x -> x, s
  | Uv (i,_,_) when in_sub i s ->
      let t = !last_sub_lookup in
      let t', s = whd s t in
      t', if t == t' then s else set_sub i t' s
  | Uv _ as x -> x, s
  | Tup v as x ->
      let hd = IA.get 0 v in
      let hd', s = whd s hd in
      match hd' with
      | Bin (n_lam,b) ->
        let n_args = IA.len v - 1 in
        if n_lam = n_args then
          whd s (beta 0 b 1 n_args v)
        else if n_lam < n_args then
          whd s (mkApp (beta 0 b 1 n_lam v) v (n_lam+1) (n_args+1))
        else
          let diff = n_lam - n_args in
          Bin(diff, beta diff b 1 n_args v), s
      | _ ->
          if hd == hd' then x, s
          else mkApp hd' (IA.tl v) 0 (IA.len v-1), s
          
end (* }}} *)

open Red
open LP

exception UnifFail of string lazy_t

let _ = Trace.pr_exn
  (function UnifFail s -> "unif: "^Lazy.force s | _ -> raise Trace.Unknown)

let fail s = raise (UnifFail (lazy s))
let lfail l = raise (UnifFail l)

let print_unif_prob s a b =
  on_buffer (fun fmt () ->
    Format.fprintf fmt "@[%a@ = %a@]%!"
      (LP.printf []) (apply_subst s a)
      (LP.printf []) (apply_subst s b))
  ()

let cst_lower xs lvl =
  IA.filter (function Con(_,l) -> l <= lvl | _ -> false) xs
let (^=) = cst_lower

let rec position_of i stop v = (); fun x ->
  if i = stop then assert false
  else if LP.equal x (IA.get i v) then DB(stop - i)
  else position_of (i+1) stop v x

let select what where =
  IA.map (position_of 0 (IA.len where) where) what
let (^-) = select
let (^--) x v = position_of 0 (IA.len v) v x

let rec unify a b s = TRACE "U" (print_unif_prob s a b)
  match a,b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ ->
      if equal a b then s else fail "rigid"
  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | Bin(nx,x), (Con _| DB _|Ext _ as y) -> unify x (eta nx y) s
  | (Con _| DB _|Ext _ as y), Bin(nx,x) -> unify x (eta nx y) s
  | Uv (_,_,a), Uv (_,_,b) when a <> b -> fail "type"
  | Uv(i,_,a), Uv(j,_,b) when i = j && a = b -> s
  | Uv(i,_,_), _ when in_sub i s -> unify !last_sub_lookup b s
  | _, Uv(j,_,_) when in_sub j s -> unify a !last_sub_lookup s
  | Uv (_,lvl1,_), Uv (id,lvl2,_) when lvl2 > lvl1 -> unify_uv id lvl2 a s
  | Uv (id,lvl,_), _ -> unify_uv id lvl b s
  | _, Uv (id,lvl,_) -> unify_uv id lvl a s
  | Tup xs, _ -> let b, s = whd s b in unify_app xs b s
  | _, Tup ys -> let a, s = whd s a in unify_app ys a s
  | _ -> fail "generic"
and eta n t =
  fixTup (IA.init (n+1) (fun i -> if i = 0 then (lift n t) else DB i))
and unify_uv id lvl t s =
  if check_scope (ref false) 0 id lvl t then set_sub id t s
  else fail "occurcheck"
and check_scope prune n id lvl t = match t with
  | Uv (i,_,_) when i = id -> false
  | Uv (i,l,_) when l > lvl ->
      prune := true;
      Printf.eprintf "prune Uv %d at the level of %d that is %d\n%!" i id lvl;
      false
  | Con (_,l) when l > lvl -> false
  | DB m when m - n > lvl -> Printf.eprintf "DB %d with %d%!" m id; false
  | Bin (ns,t) -> check_scope prune (n+ns) id lvl t
  | Tup xs -> IA.for_all (check_scope prune n id lvl) xs
  | _ -> true
and rel_higher lvl = function (DB l | Con(_,l)) -> l > lvl | _ -> false
and rigid = function Uv _ -> false | _ -> true
and isPU xs =
  match IA.get 0 xs with
  | Uv (id,lvl,_) -> IA.for_alli (fun i x -> i = 0 || rel_higher lvl x) xs
  | _ -> false
and unify_app v t s =
  let rv, s =  whd s (Tup v) in
  TRACE "A" (print_unif_prob s rv t)
  match rv, t with
  | Tup xs, Tup ys
    when IA.len xs = IA.len ys && rigid (IA.get 0 xs) && rigid (IA.get 0 ys) ->
      IA.fold2 unify xs ys s
  | ((Tup xs, y) | (y, Tup xs)) when isPU xs ->
    (match IA.get 0 xs with
    | Uv (id,lvl,_) ->
(*                     CHECK MILLER PATTERN LINEARITY *)
(*
        let nargs = IA.len xs-1 in
        let args = IA.sub 1 nargs xs in
        let y = Bin(nargs, bind 0 t args) in
        let do_prune = ref false in
        if check_scope do_prune 0 id lvl y then set_sub id y s
        else if !do_prune then
*)
(*           let args = IA.filter (function Con(_,l) -> l > lvl | _ -> false) args in *)
        let nargs = IA.len xs-1 in
        let args = IA.sub 1 nargs xs in
          let y', s = let y, s = prune 0 args lvl t s in Bin(nargs,y), s in
          Format.eprintf "pruned for %d: %a -> %a\n%!" id
            (LP.printf []) y
            (LP.printf []) y';
          set_sub id y' s
(*         else fail "hounif" *)
    | _ -> assert false)
  | t1, t2 -> fail "founif"
and prune depth csts lvl t s =
  match t with
  | Uv(i,l,_) when in_sub i s -> prune depth csts lvl !last_sub_lookup s
  | Uv(i,l,a) when l > lvl ->
      let m, s = fresh_uv lvl a s in
      let al = IA.init (depth + IA.len csts) (fun i ->
(*           if i = 0 then m *)
          (*else*) if i < IA.len csts then Red.lift depth (IA.get i csts)
          else DB(IA.len csts + depth - i)) in
      let cs = al ^= l in
      let ws = cs ^- al in
      let bs = IA.of_array [||] in
      let zl = IA.of_array [||] in (* almost al *)
      let us = zl ^- bs in
      let vs = zl ^- al in
      let pp s x = Format.eprintf "%s = %a\n%!" s (LP.printf []) (Tup x) in
      pp "cs" cs;
      pp "ws" ws;
      Printf.eprintf "Uv %d takes %s\n%!" i (print m);
(*       let t = if depth + IA.len csts = 0 then m else Tup al in *)
      let s = set_sub i
        ((*Bin(0,*)mkApp m (IA.append cs us) 0 (IA.len cs + IA.len us)) s in
      mkApp m (IA.append ws vs) 0 (IA.len ws + IA.len vs), s
  | Con(_,l) as x when l <= lvl -> x, s
  | (Con _ | DB _) as x ->
      let al = IA.init (depth + IA.len csts) (fun i ->
(*           if i = 0 then m *)
          (*else*) if i < IA.len csts then Red.lift depth (IA.get i csts)
          else DB(IA.len csts + depth - i)) in
      x ^-- al, s                
  | Bin(ns,x) -> let x, s = prune (depth+ns) csts lvl x s in Bin(ns,x), s
  | Tup xs -> let xs, s = IA.fold_map (prune depth csts lvl) xs s in fixTup xs, s
  | x -> x, s
(*
and position_of x orig i stop v =
  if i = stop then orig
  else if LP.equal x (IA.get i v) then DB(stop - i)
  else position_of x orig (i+1) stop v
and bind depth t v =
  match t with
  | (Ext _ | Uv _) as x -> x
  | Con _ as x -> position_of x x 0 (IA.len v) v
  | DB n as x -> position_of (DB(n-depth)) x 0 (IA.len v) v
  | Tup xs -> Tup(IA.map (fun t -> bind depth t v) xs)
  | Bin(ns,b) -> Bin(ns,bind (depth+ns) t v)
*)

exception NoClause

let mkhv =
  let i = ref 0 in
  fun depth -> incr i; Con("h"^string_of_int !i,depth)

let contextualize depth s t hv =
  let t = Subst.refresh_uv depth s t in
  if hv <> [] then
    beta 0 t 0 (List.length hv) (IA.of_list (List.rev hv))
  else t
let rec contextualize_premise depth s hv = function
  | Atom t -> Atom(contextualize depth s t hv)
  | Impl(t,h) ->
      Impl(contextualize depth s t hv,
           contextualize_premise depth s hv h)
  | Pi(n,h) -> Pi(n,contextualize_premise depth s (mkhv (depth+1)::hv) h)

let rec select goal depth s = function
  | [] ->
      Printf.eprintf "fail: %s\n%!" (LP.print (apply_subst s goal));
      raise NoClause
  | (nuv,hd,hyps) as clause :: prog ->
      try
        let hd = contextualize depth s hd [] in
        let hyps =
          List.fold_right (fun h hs ->
                  (depth, contextualize_premise depth s [] h) :: hs)
          hyps [] in
        let s = Subst.set_top (Subst.top s + nuv + 1) s in
        let s = unify goal hd s in
        Format.eprintf "@[<hv2>  use:@ %a@]@\n%!" print_clausef clause;
        Format.eprintf "@[<hv2>  sub:@ %a@]@\n%!" Subst.print_substf s;
        s, hyps, prog
      with UnifFail _ -> select goal depth s prog
let rec run prog s (depth,goal) =
  match goal with
  | Atom goal ->
    let rec aux alternatives =
      Format.eprintf "@[<hv2>on:@ %a%s@]@\n%!"
        (LP.printf []) (apply_subst s goal)
        (if debug then Printf.sprintf " (%d,%d)" depth (Subst.top s) else "");
      let s, goals, alternatives = select goal depth s alternatives in
      try List.fold_left (run prog) s goals
      with NoClause -> aux alternatives in
    aux prog
  | Pi(_,goal) -> run prog s (depth+1,goal)
  | Impl(hyp,goal) -> run ((LP.max_uv hyp 0,hyp,[]) :: prog) s (depth,goal)
let run p g =
  let n = fold_premise (LP.fold max_uv) g 0 in
  run p (empty (n + 1)) (0,g)

(* vim:set foldmethod=marker: *)
