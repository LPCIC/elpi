(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Lpdata
open LP
open Subst
open Red

(* Based on " An Implementation of the Language Lambda Prolog Organized around
   Higher-Order Pattern Unification", Xiaochu Qi (pages 51 and 52)
   or "Practical Higher-Order Pattern Unification With On-the-Fly Raising",
   Gopalan Nadathur and Natalie Linnell. LNCS 3668 *)

exception UnifFail of string lazy_t

let _ = Trace.pr_exn
  (function UnifFail s -> "unif: "^Lazy.force s | _ -> raise Trace.Unknown)

let fail s = raise (UnifFail (lazy s))
let lfail l = raise (UnifFail l)

let print_unif_prob s rel a b fmt =
  Format.fprintf fmt "@[%a@ %s %a@]%!"
    (prf_data []) (apply_subst s a) rel (prf_data []) (apply_subst s b)

let rec rigid x = match x with
  | Uv _ -> false
  | App xs -> rigid (look (L.hd xs))
  | _ -> true

let eta n t = TRACE "eta" (fun fmt -> prf_data [] fmt t)
 let t =
   fixApp (L.init (n+1) (fun i -> if i = 0 then (lift n t) else mkDB (n+1-i))) in
 SPY "etaed" (prf_data []) t;
 t

let inter xs ys = L.filter (fun x -> not(L.for_all (equal x) ys)) xs

(* construction of bindings: ↓ is ^- and ⇑ is ^= *)
let cst_lower xs lvl =
  L.filter (fun x -> match look x with Con(_,l) -> l <= lvl | _ -> false) xs
let (^=) = cst_lower

let position_of l = let stop = L.len l in fun x ->
  let rec aux i = function
    | [] -> fail "cannot occur"
    | y::ys -> if equal x y then mkDB (stop - i) else aux (i+1) ys
  in aux 0 (L.to_list l)
let (^-) what where = L.map (position_of where) what
let (^--) x v = position_of v x

let mk_al nbinders args =
  (* builds: map (lift nbinders) args @ [DB nbinders ... DB 1] *)
  let nargs = L.len args in
  L.init (nbinders + nargs)
    (fun i ->
      if i < nargs then Red.lift nbinders (L.get i args)
      else mkDB (nargs + nbinders - i))

(* pattern unification fragment *)
let higher lvl x = match look x with (DB l | Con(_,l)) -> l > lvl | _ -> false
let isPU xs =
  match look (L.get 0 xs) with
  | Uv (_,lvl) -> L.for_all (higher lvl) (L.tl xs) && L.uniq LP.equal (L.tl xs)
  | _ -> false

let rec bind x id depth lvl args t s =
  let t, s = whd s t in
  TRACE "bind" (print_unif_prob s (":= "^string_of_int depth^"↓") x t)
  match look t with
  | Bin(m,t) -> let t, s = bind x id (depth+m) lvl args t s in mkBin m t, s
  | Ext _ -> t, s
  | Con (_,l) when l <= lvl -> t, s
  | Con _ -> t ^-- mk_al depth args, s (* XXX optimize *)
  (* the following 2 cases are: t ^-- mk_al depth args, s *) (* XXX CHECK *)
  | DB m when m <= depth -> t, s
  | DB m -> lift depth (mkDB (m-depth) ^-- args), s
  | Seq(xs,tl) ->
      let xs, s = L.fold_map (bind x id depth lvl args) xs s in
      let tl, s = bind x id depth lvl args tl s in
      mkSeq xs tl, s
  | Nil -> t, s
  | App bs as t when rigid t ->
      let ss, s = L.fold_map (bind x id depth lvl args) bs s in
      mkApp ss, s
  | (App _ | Uv _) as tmp -> (* pruning *)
      let bs = match tmp with
        | App bs -> bs | Uv _ -> L.singl t | _ -> assert false in
      match look (L.hd bs) with
      | (Bin _ | Con _ | DB _ | Ext _ | App _ | Seq _ | Nil) -> assert false
      | Uv(j,l) when j <> id && l > lvl && isPU bs ->
          let bs = L.tl bs in
          let nbs = L.len bs in
          let h, s = fresh_uv lvl s in
          let al = mk_al depth args in
          let cs = al ^= l in (* constants X = id,lvl can copy *)
          let ws = cs ^- al in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- al in
          let us = zs ^- bs in
          let nws, nvs, ncs, nus = L.len ws, L.len vs, L.len cs, L.len us in
          let vj = mkBin nbs (mkAppv h (L.append cs us) 0 (ncs + nus)) in
          let s = set_sub j vj s in
          let t = mkAppv h (L.append ws vs) 0 (nws+nvs) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s
      | Uv(j,l) when j <> id && isPU bs ->
          let bs = L.tl bs in
          let nbs = L.len bs in
          let h, s = fresh_uv (*lv*)l s in
          let cs = bs ^= lvl in (* constants X = id,lvl can copy *)
          let ws = cs ^- bs in
          let al = mk_al depth args in
          let zs = inter al bs in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- bs in
          let us = zs ^- al in
          let nws, nvs, ncs, nus = L.len ws, L.len vs, L.len cs, L.len us in
          let vj = mkBin nbs (mkAppv h (L.append ws vs) 0 (nws + nvs)) in
          let s = set_sub j vj s in
          let t = mkAppv h (L.append cs us) 0 (ncs+nus) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s
      | Uv _ -> fail "ho-ho"

let mksubst x id lvl t args s =
  let nargs = L.len args in
(*
  match look t with
  | Bin(k,Uv(id1,_)) when id1 = id -> assert false (* TODO *)
  | Bin(k,App xs) when equal (L.get 0 xs) (Uv (id,lvl)) && isPU xs ->
      assert false (* TODO *)
  | _ ->
*)
     let t, s = bind x id 0 lvl args t s in
     set_sub id (mkBin nargs t) s

let rec splay xs tl s =
  let tl, s = whd s tl in
  match look tl with
  | Uv _ | Nil -> xs, tl, s
  | Seq(ys,t) -> splay (L.append xs ys) t s
  | _ -> assert false

let rec unify a b s = TRACE "unify" (print_unif_prob s "=" a b)
  let a, s =  whd s a in
  let b, s =  whd s b in
  match look a, look b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ | Nil, Nil ->
      if equal a b then s else fail "rigid"
  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | ((Bin(nx,x), y) | (y, Bin(nx,x))) when rigid y -> unify x (eta nx (kool y)) s
  | Uv(i,_), Uv(j,_) when i = j -> s
  | x, y -> if rigid x && rigid y then unify_fo x y s else unify_ho x y s
and unify_fo x y s =
  match x, y with
  | App xs, App ys when L.len xs = L.len ys -> L.fold2 unify xs ys s
  | Seq(xs,tl), Seq(ys,sl) ->
      let xs, tl, s = splay xs tl s in
      let ys, sl, s = splay ys sl s in
      let nxs, nys = L.len xs, L.len ys in
      if nxs = nys then unify tl sl (L.fold2 unify xs ys s)
      else if nxs < nys && not (rigid (look tl)) then
        let yshd, ystl = L.sub 0 nxs ys, L.sub nxs (nys - nxs) ys in
        unify tl (mkSeq ystl mkNil) (L.fold2 unify xs yshd s)
      else if nxs > nys && not (rigid (look sl)) then
        let xshd, xstl = L.sub 0 nys xs, L.sub nys (nxs - nys) xs in
        unify sl (mkSeq xstl mkNil) (L.fold2 unify ys xshd s)
      else fail "listalign"
  | _ -> fail "founif"
and unify_ho x y s =
  match x, y with
  | (((Uv (id,lvl) as x), y) | (y, (Uv (id,lvl) as x))) ->
      mksubst (kool x) id lvl (kool y) L.empty s
  | (((App xs as x), y) | (y, (App xs as x))) when isPU xs -> begin
      match look (L.hd xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (L.tl xs) s
      | _ -> assert false
    end
  | _ -> fail "not a pattern unif"

(* ******************************** Main loop ******************************* *)

exception NoClause
type objective =
  [ `Atom of data * key
  | `Unify of data * data | `Custom of string * data | `Cut ]
type goal = int * objective * program * program * int
type alternatives = (subst * goal list) list
type step_outcome = subst * goal list * alternatives


(* Important: when we move under a pi we put a constant in place of the
 * bound variable. This way hypothetical clauses do not need to be lifted
 * when we move under other pi binders *)
let mkhv_aux =
  let i = ref 0 in
  let small_digit = function
    | 0 -> "₀" | 1 -> "₁" | 2 -> "₂" | 3 -> "₃" | 4 -> "₄" | 5 -> "₅"
    | 6 -> "₆" | 7 -> "₇" | 8 -> "₈" | 9 -> "₉" | _ -> assert false in
  let rec digits_of n = n mod 10 :: if n > 10 then digits_of (n / 10) else [] in
  fun depth ->
    incr i;
    mkCon ("𝓱"^
      String.concat "" (List.map small_digit (List.rev (digits_of !i)))) depth
let rec mkhv n d =
  if n = 0 then []
  else mkhv_aux d :: mkhv (n-1) d
let ctx_of_hv l =
  List.map (fun x -> match look x with
    | (Con _ | Uv _) -> LP.string_of_data x
    | _ -> assert false) l

let rec fresh_uv n d s =
  if n = 0 then [], s
  else 
    let m, s = Subst.fresh_uv d s in
    let tl, s = fresh_uv (n-1) d s in
    m :: tl, s

let rec iter_sep spc pp fmt = function
  | [] -> Format.fprintf fmt ""
  | [x] -> pp fmt x; Format.fprintf fmt "@ "
  | x::tl -> pp fmt x; spc fmt (); iter_sep spc pp fmt tl

let pr_cur_goal g lvl s fmt =
  match g with
  | `Atom (goal,_) ->
      Format.fprintf fmt "%d |- %a"
        lvl (prf_data []) (apply_subst s goal)
  | `Unify(a,b) ->
      Format.fprintf fmt "%a = %a"
          (prf_data []) (apply_subst s a) (prf_data []) (apply_subst s b)
  | `Custom(name,a) ->
      Format.fprintf fmt "%s %a" name (prf_data []) (apply_subst s a)
  | `Cut -> Format.fprintf fmt "!"
let pr_cur_goals gls s fmt =
  Format.fprintf fmt "@[<hov 0>"; 
  iter_sep (fun fmt () -> Format.fprintf fmt ",@ ")
    (fun fmt (_,g,_,_,l) -> pr_cur_goal g l s fmt) fmt gls;
  Format.fprintf fmt "@]" 

let custom_tab = ref []
let register_custom n f = custom_tab := ("$"^n,f) :: !custom_tab
let custom name t s d p =
  try List.assoc name !custom_tab t s d p
  with Not_found -> raise(Invalid_argument ("custom "^name))

let contextualize depth t hv =
  SPY "hv" (iter_sep Format.pp_print_space (prf_data [])) hv;
  SPY "premise" (prf_data []) t;
  assert(depth = 0);
  Red.beta_under depth t (List.rev hv)

let add_cdepth b cdepth =
  List.map (fun (hv,p) -> cdepth, hv, (if b then key_of p else Flex), p)

let mkAtom t hv = `Atom(contextualize 0 t hv, key_of (Atom t))

let contextualize_premise ?(compute_key=false) depth subst old_hv premise =
  let rec aux cdepth depth s hv eh = function
  | Atom t ->
      [cdepth, mkAtom t hv, add_cdepth compute_key cdepth eh], s
  | AtomBI (BIUnif(x,y)) ->
      [cdepth, `Unify(contextualize 0 x hv,contextualize 0 y hv),
       add_cdepth compute_key cdepth eh], s
  | AtomBI (BICustom(n,x)) ->
      [cdepth, `Custom(n,contextualize 0 x hv),
       add_cdepth compute_key cdepth eh], s
  | AtomBI BICut ->
      [cdepth, `Cut, add_cdepth compute_key cdepth eh], s
  | Impl(Conj ps,h) ->
      aux cdepth depth s hv (List.map (fun p -> hv,p) ps @ eh) h
  | Impl(p,h) -> aux cdepth depth s hv ((hv,p) :: eh) h
  | Pi(n,h) -> aux (cdepth+n) depth s (mkhv n (depth+1) @ hv) eh h
  | Sigma(n,h) ->
      let ms, s = fresh_uv n cdepth s in
      aux cdepth depth s (ms @ hv) eh h
  | Conj l ->
      let ll, s = List.fold_right (fun p (acc,s) ->
        let l, s = aux cdepth depth s hv eh p in
        l::acc, s) l ([],s) in
      List.flatten ll, s
  in
    aux depth depth subst old_hv [] premise

let contextualize_hyp depth subst hv premise =
  match contextualize_premise depth subst hv premise with
  | [_,`Atom(hd,_),hyps], s -> hd, hyps, s
  | [], _ -> assert false
  | _ -> assert false

let contextualize_goal depth subst hv goal =
  contextualize_premise ~compute_key:true depth subst hv goal

let no_key_match k kc =
  match k, kc with
  | Key t1, Key t2 -> not(LP.equal t1 t2)
  | Key _, Flex -> true
  | Flex, _ -> false

let select k goal depth (s as os) prog orig_prog lvl : step_outcome =
  let rec first = function
  | [] ->
      SPY "fail" (prf_data []) (apply_subst s goal);
      raise NoClause
  | (_,old_hv,kc,clause) :: rest when no_key_match k kc -> first rest
  | (_,old_hv,_,clause) :: rest ->
      try
        let hd, subgoals, s = contextualize_hyp depth s old_hv clause in
        let s = unify goal hd s in
        SPY "selected" (prf_clause (ctx_of_hv old_hv)) clause;
        SPY "sub" Subst.prf_subst s;
        let subgoals, s =
          List.fold_right (fun (d,hv,_,p) (acc,s) ->
            let gl, s = contextualize_goal d s hv p in
            gl :: acc, s) subgoals ([],s) in
        let subgoals =
          List.map (fun (d,g,e) -> d,g,e@orig_prog,e@orig_prog,lvl+1)
            (List.flatten subgoals) in
        s, subgoals, [os,[depth,`Atom(goal,k),rest,orig_prog,lvl]]
      with UnifFail _ ->
        SPY "skipped" (prf_clause (ctx_of_hv old_hv)) clause;
        first rest
  in
    first prog

let rec run1 s ((depth,goal,prog,orig_prog,lvl) : goal) : step_outcome =
  match goal with
  | `Cut -> assert false
  | `Atom(t,k) ->
      let s, goals, alts = select k t depth s prog orig_prog lvl in
      s, goals, alts
  | `Unify(a,b) ->
      (try
        let s = unify a b s in
        SPY "sub" Subst.prf_subst s;
        s,[], []
      with UnifFail _ -> raise NoClause)
  | `Custom(name,a) ->
      try
        let s = custom name a s depth prog in
        SPY "sub" Subst.prf_subst s;
        s,[], []
      with UnifFail _ -> raise NoClause

let rec cut lvl = function
  | [] -> []
  | (_,(_,_,_,_,l)::_) :: xs when l + 1 = lvl -> xs
  | _ :: xs -> cut lvl xs

let rec run s (gls : goal list) alts : subst * alternatives =
  let s, subg, alts =
    match gls with
    | [] -> s, [], alts
    | (_,`Cut,_,_,lvl)::rest ->
       let alts = cut lvl alts in
       s, rest, alts
    | (_,go,_,_,lvl as g)::rest ->
       try
         TRACE "run" (pr_cur_goal go lvl s)
         let s, subg, new_alts = run1 s g in
         s, (subg@rest),
           (List.map (fun (s,gl) -> s,gl @ rest) new_alts @ alts)
       with
       | NoClause as e ->
           match alts with
           | [] -> raise e
           | (s,g) :: rest ->
               SPY "backtrack" (fun fmt s -> pr_cur_goals gls s fmt) s;
               s, g, rest
  in
  if subg = [] then s, alts
  else run s subg alts

let prepare_initial_goal g =
  let s = empty 1 in
  match g with
  | Sigma(n,g) ->
      let ms, s = fresh_uv n 0 s in
      ms, g, s
  | _ -> [], g, s

let run (p : program) (g : premise) =
  let hv, g, s = prepare_initial_goal g in
  Format.eprintf "@[<hv2>goal:@ %a@]@\n%!" (prf_goal (ctx_of_hv hv)) g;
  let gls, s = contextualize_goal 0 s hv g in
  let s,_ = run s (List.map (fun (d,g,ep) -> (d,g,ep@p,ep@p,0)) gls) [] in
  fst(fold_map_premise 0 (fun i t () ->
    let n = List.length hv in
    let vhv = if hv = [] then L.empty else L.of_list (List.rev hv) in
    let v = L.append vhv (L.init i (fun j -> mkDB(i-j))) in
    fst(Red.whd s (mkAppv (mkBin (i+n) t) v 0 (L.len v))), ()) g ()), s

(* vim:set foldmethod=marker: *)
