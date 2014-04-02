open Lpdata
open LP
open Subst
open Red

exception UnifFail of string lazy_t

let _ = Trace.pr_exn
  (function UnifFail s -> "unif: "^Lazy.force s | _ -> raise Trace.Unknown)

let fail s = raise (UnifFail (lazy s))
let lfail l = raise (UnifFail l)

let print_unif_prob s rel a b fmt =
  Format.fprintf fmt "@[%a@ %s %a@]%!"
    (printf []) (apply_subst s a) rel (printf []) (apply_subst s b)

let rec rigid = function
  | Uv _ -> false
  | Tup xs -> rigid (IA.get 0 xs)
  | _ -> true

let eta n t =
  fixTup (IA.init (n+1) (fun i -> if i = 0 then (lift n t) else DB (n-i)))

let inter xs ys = IA.filter (fun x -> not(IA.for_all (equal x) ys)) xs

(* construction of bindings: ↓ is ^- and ⇑ is ^= *)
let cst_lower xs lvl = IA.filter (function Con(_,l) -> l <= lvl | _ -> false) xs
let (^=) = cst_lower

let rec position_of i stop v = (); fun x ->
  if i = stop then fail "cannot occur"
  else if equal x (IA.get i v) then DB(stop - i)
  else position_of (i+1) stop v x
let (^-) what where = IA.map (position_of 0 (IA.len where) where) what
let (^--) x v = position_of 0 (IA.len v) v x

let mk_al nbinders args =
  (* builds: map (lift nbinders) args @ [DB nbinders ... DB 1] *)
  let nargs = IA.len args in
  IA.init (nbinders + nargs)
    (fun i ->
      if i < nargs then Red.lift nbinders (IA.get i args)
      else DB(nargs + nbinders - i))

(* pattern unification fragment *)
let higher lvl = function (DB l | Con(_,l)) -> l > lvl | _ -> false
let rec not_in v len i x =
  if i+1 = len then true
  else not(equal x (IA.get (i+1) v)) && not_in v len (i+1) x
let isPU xs =
  match IA.get 0 xs with
  | Uv (_,lvl) ->
      IA.for_alli (fun i x -> i = 0 || higher lvl x) xs &&
      IA.for_alli (fun i x -> i = 0 || not_in xs (IA.len xs) i x) xs
  | _ -> false

(* Based on Xiaochu Qi PHD (pages 51..52) / or reference 41 *)
let rec bind x id depth lvl args t s =
  let t, s = whd s t in
  TRACE "bind" (print_unif_prob s (":= "^string_of_int depth^"↓") x t)
  match t with
  | Bin(m,t) -> let t, s = bind x id (depth+m) lvl args t s in Bin(m,t), s
  | Ext _ -> t, s
  | Con (_,l) when l <= lvl -> t, s
  | Con _ -> t ^-- mk_al depth args, s (* XXX optimize *)
  (* the following 2 cases are: t ^-- mk_al depth args, s *) (* XXX CHECK *)
  | DB m when m <= depth -> t, s
  | DB m -> lift depth (DB(m-depth) ^-- args), s
  | Uv(j,l) -> bind x id depth lvl args (Tup(IA.of_array[|t|])) s
  | Tup bs when rigid t ->
      let ss, s = IA.fold_map (bind x id depth lvl args) bs s in
      Tup ss, s
  | Tup bs -> (* pruning *)
      match IA.get 0 bs with
      | (Bin _ | Con _ | DB _ | Ext _ | Tup _) -> assert false
      | Uv(j,l) when j <> id && l > lvl && isPU bs ->
          let bs = IA.tl bs in
          let nbs = IA.len bs in
          let h, s = fresh_uv lvl s in
          let al = mk_al depth args in
          let cs = al ^= l in (* constants X = id,lvl can copy *)
          let ws = cs ^- al in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- al in
          let us = zs ^- bs in
          let nws, nvs, ncs, nus = IA.len ws, IA.len vs, IA.len cs, IA.len us in
          let vj = mkBin nbs (mkApp h (IA.append cs us) 0 (ncs + nus)) in
          let s = set_sub j vj s in SPY "vj" (printf []) vj;
          let t = mkApp h (IA.append ws vs) 0 (nws+nvs) in SPY "t" (printf[]) t;
          t, s
      | Uv(j,l) when j <> id && isPU bs ->
          let bs = IA.tl bs in
          let nbs = IA.len bs in
          let h, s = fresh_uv lvl s in
          let cs = bs ^= lvl in (* constants X = id,lvl can copy *)
          let ws = cs ^- bs in
          let al = mk_al depth args in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- bs in
          let us = zs ^- al in
          let nws, nvs, ncs, nus = IA.len ws, IA.len vs, IA.len cs, IA.len us in
          let vj = mkBin nbs (mkApp h (IA.append ws vs) 0 (nws + nvs)) in
          let s = set_sub j vj s in SPY "vj" (printf []) vj;
          let t = mkApp h (IA.append cs us) 0 (ncs+nus) in SPY "t" (printf[]) t;
          t, s
      | Uv _ -> fail "ho-ho"

let mksubst x id lvl t args s =
  let nargs = IA.len args in
  match t with
  | Bin(k,Uv(id1,_)) when id1 = id -> assert false (* TODO *)
  | Bin(k,Tup xs) when equal (IA.get 0 xs) (Uv (id,lvl)) && isPU xs ->
      assert false (* TODO *)
  | _ ->
     let t, s = bind x id 0 lvl args t s in
     set_sub id (mkBin nargs t) s

let rec unify a b s = TRACE "unify" (print_unif_prob s "=" a b)
  let a, s =  whd s a in
  let b, s =  whd s b in
  match a, b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ ->
      if equal a b then s else fail "rigid"
  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | ((Bin(nx,x), y) | (y, Bin(nx,x))) when rigid y -> unify x (eta nx y) s
  | Uv(i,_), Uv(j,_) when i = j -> s
  | x, y -> if rigid x && rigid y then unify_fo x y s else unify_ho x y s
and unify_fo x y s =
  match x, y with
  | Tup xs, Tup ys when IA.len xs = IA.len ys -> IA.fold2 unify xs ys s
  | _ -> fail "founif"
and unify_ho x y s =
  match x, y with
  | (((Uv (id,lvl) as x), y) | (y, (Uv (id,lvl) as x))) ->
      mksubst x id lvl y (IA.init 0 (fun _ -> y)) s
  | (((Tup xs as x), y) | (y, (Tup xs as x))) when isPU xs -> begin
      match IA.get 0 xs with
      | Uv (id,lvl) -> mksubst x id lvl y (IA.tl xs) s
      | _ -> assert false
    end
  | _ -> fail "not a pattern unif"

(* ******************************** Main loop ******************************* *)

exception NoClause

(* Important: when we move under a pi we put a constant in place of the
 * bound variable. This was hypothetical clauses do not need to be lifted
 * when we move under other pi binders *)
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
      Printf.eprintf "fail: %s\n%!" (print (apply_subst s goal));
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
        (printf []) (apply_subst s goal)
        (if !Trace.debug then Printf.sprintf " (%d,%d)" depth (Subst.top s)
        else "");
      let s, goals, alternatives = select goal depth s alternatives in
      try List.fold_left (run prog) s goals
      with NoClause -> aux alternatives in
    aux prog
  | Pi(_,goal) -> run prog s (depth+1,goal)
  | Impl(hyp,goal) -> run ((max_uv hyp 0,hyp,[]) :: prog) s (depth,goal)
let run p g =
  let n = fold_premise (fold max_uv) g 0 in
  run p (empty (n + 1)) (0,g)

(* vim:set foldmethod=marker: *)
