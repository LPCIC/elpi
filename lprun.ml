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

let inter xs ys s =
  L.filter (fun x -> let x = Red.nf s x in
                     not(L.for_all (fun y ->
                                    let y = Red.nf s y in
                                    not(equal x y)) ys)) xs

(* construction of bindings: ↓ is ^- and ⇑ is ^= *)
let cst_lower xs lvl =
  L.filter (fun x -> match look x with Con(_,l) -> l <= lvl | _ -> false) xs
let (^=) = cst_lower

let position_of s l = let stop = L.len l in fun x ->
        let x = Red.nf s x in
  let rec aux i = function
    | [] -> fail "cannot occur"
    | y::ys -> 
        let y = Red.nf s y in
                    if equal x y then mkDB (stop - i) else aux (i+1) ys
  in aux 0 (L.to_list l)
let ($) f x = f x
let (^-) what where s = L.map (position_of s where) what
let (^--) x v s = position_of s v x

let mk_al nbinders args =
  (* builds: map (lift nbinders) args @ [DB nbinders ... DB 1] *)
  let nargs = L.len args in
  L.init (nbinders + nargs)
    (fun i ->
      if i < nargs then Red.lift nbinders (L.get i args)
      else mkDB (nargs + nbinders - i))

(* pattern unification fragment *)
let higher nf lvl x =
  match look (nf x) with Con(_,l) -> l > lvl | DB _ -> true | _ -> false
let isPU s xs =
        TRACE "isPU" (fun fmt -> prf_data [] fmt (mkApp xs))
  match look (L.hd xs) with
  | Uv (_,lvl) ->
      let nf t = fst (whd s t) in
      L.for_all (higher nf lvl) (L.tl xs) &&
      L.uniq LP.equal (L.map nf (L.tl xs))
  | _ -> false

let rec bind x id depth lvl args t s =
  let t, s = whd s t in
  TRACE "bind" (print_unif_prob s (":= "^string_of_int depth^"↓") x t)
  match look t with
  | Bin(m,t) -> let t, s = bind x id (depth+m) lvl args t s in mkBin m t, s
  | Ext _ -> t, s
  | Con (_,l) when l <= lvl -> t, s
  | Con _ -> t ^-- mk_al depth args $ s, s (* XXX optimize *)
  (* the following 2 cases are: t ^-- mk_al depth args, s *) (* XXX CHECK *)
  | DB m when m <= depth -> t, s
  | DB m -> lift depth (mkDB (m-depth) ^-- args $ s), s
  | Seq(xs,tl) ->
      let xs, s = L.fold_map (bind x id depth lvl args) xs s in
      let tl, s = bind x id depth lvl args tl s in
      mkSeq xs tl, s
  | Nil -> t, s
  | App bs as t when rigid t ->
      let ss, s = L.fold_map (bind x id depth lvl args) bs s in
      mkApp ss, s
  | VApp _ -> assert false
  | (App _ | Uv _) as tmp -> (* pruning *)
          SPY "Pruning" (prf_data []) (mkNil);
      let bs = match tmp with
        | App bs -> bs | Uv _ -> L.singl t | _ -> assert false in
      match look (L.hd bs) with
      | (Bin _ | Con _ | DB _ | Ext _ | App _ | Seq _ | Nil | VApp _) -> assert false
      | Uv(j,l) when j <> id && l > lvl && isPU s bs ->
          SPY "1hd" (prf_data []) (L.hd bs);
          let bs = L.tl bs in
          let nbs = L.len bs in
          let h, s = fresh_uv lvl s in
          let al = mk_al depth args in
          let cs = al ^= l in (* constants X = id,lvl can copy *)
          let ws = cs ^- al $ s in
          let zs = inter al bs s in (* XXX paper excludes #l-1, why? *)
          let vs = zs ^- al $ s in
          let us = zs ^- bs $ s in
          let nws, nvs, ncs, nus = L.len ws, L.len vs, L.len cs, L.len us in
          let vj = mkBin nbs (mkAppv h (L.append cs us) 0 (ncs + nus)) in
          let s = set_sub j vj s in
          let t = mkAppv h (L.append ws vs) 0 (nws+nvs) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s
      | Uv(j,l) when j <> id ->
          let bs = L.tl bs in
          let nbs = L.len bs in
          let ssrels,ssargs,s,_ =
           L.fold
            (fun e (ssrels,ssargs,s,n) ->
              try
               let e,s = bind x id depth lvl args e s in
               mkDB n::ssrels, e::ssargs, s, n-1
              with UnifFail _ -> ssrels,ssargs,s,n-1)
             bs ([],[],s,nbs) in
          let ssrels = List.rev ssrels in
          let ssargs = List.rev ssargs in
          let h, s = fresh_uv l s in
          let vj = mkBin nbs (mkApp (L.of_list (h::ssrels))) in
          let s = set_sub j vj s in
          let t = mkApp (L.of_list (h::ssargs)) in
          t, s
      (*| Uv(j,l) when j <> id && isPU s bs ->
          SPY "2hd" (prf_data []) (mkNil);
          let bs = L.tl bs in
          let nbs = L.len bs in
          let h, s = fresh_uv (*lv*)l s in
          let cs = bs ^= lvl in (* constants X = id,lvl can copy *)
          SPY "cs" (prf_data []) (mkApp cs);
          let ws = cs ^- bs $ s in
          SPY "ws" (prf_data []) (mkApp ws);
          let al = mk_al depth args in
          SPY "al" (prf_data []) (mkApp al);
          let zs = inter al bs s in (* XXX paper excludes #l-1, why? *)
          SPY "zs" (prf_data []) (mkApp zs);
          let vs = zs ^- bs $ s in
          SPY "vs" (prf_data []) (mkApp vs);
          let us = zs ^- al $ s in
          SPY "5hd" (prf_data []) (mkNil);
          let nws, nvs, ncs, nus = L.len ws, L.len vs, L.len cs, L.len us in
          let vj = mkBin nbs (mkAppv h (L.append ws vs) 0 (nws + nvs)) in
          let s = set_sub j vj s in
          let t = mkAppv h (L.append cs us) 0 (ncs+nus) in
          SPY "vj" (prf_data []) vj; SPY "t" (prf_data[]) t;
          t, s*)
      | Uv _ -> assert false (*fail "ho-ho"*)

let keep xs ys s =
  let l1 = L.to_list xs in
  let l2 = L.to_list ys in
  let rec aux l1 l2 i =
    match l1, l2 with
    | [], [] -> []
    | x::xs, y::ys when equal (Red.nf s x) (Red.nf s y) ->
       mkDB i :: aux xs ys (i-1)
    | _::xs, _::ys -> aux xs ys (i-1)
    | _ -> assert false
  in
    L.of_list (aux l1 l2 (L.len xs))

let mksubst x id lvl t args s =
  let nargs = L.len args in
  match look t with
  | App xs when isPU s xs && equal (L.get 0 xs) (mkUv id lvl) ->
      if L.for_all2 equal (L.tl xs) args then s
      else
        let h_args = keep (L.tl xs) args s in
        if L.len h_args = nargs then s
        else
          let h, s = fresh_uv lvl s in
          set_sub id (mkBin nargs (mkApp (L.cons h h_args))) s
  | _ ->
     let t, s = bind x id 0 lvl args t s in
     SPY "mksubst" (prf_data []) (mkBin nargs t);
     set_sub id (mkBin nargs t) s

let rec splay xs tl s =
  let tl, s = whd s tl in
  match look tl with
  | Uv _ | Nil -> xs, tl, s
  | Seq(ys,t) -> splay (L.append xs ys) t s
  | _ -> xs, tl, s

let rec unify a b s = TRACE "unify" (print_unif_prob s "=" a b)
  let a, s =  whd s a in
  let b, s =  whd s b in
  match look a, look b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ | Nil, Nil ->
      if equal a b then s else fail "rigid"
  | VApp _, _ -> assert false
  | Bin _, VApp _ -> assert false
  | t, VApp(true,t1,t2) when not(rigid t) ->
     let hd, tl = match t with
       | App xs -> L.hd xs, L.tl xs | Uv _ -> a, L.empty | _ -> assert false in
     let s = unify hd t1 s in
     unify (mkSeq tl mkNil) t2 s
  | t, VApp(false,t1,t2) when Subst.is_tc a ->
     let hd, tl = match t with
       | App xs -> L.hd xs, L.tl xs | Con _ -> a, L.empty | _ -> assert false in
     let s = unify hd t1 s in
     unify (mkSeq tl mkNil) t2 s
  | _, VApp (b,_,_) -> if b then fail "not flex" else fail "not rigid"
  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | ((Bin(nx,x), y) | (y, Bin(nx,x))) when rigid y ->unify x (eta nx (kool y)) s
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
  | (y, (App xs as x)) when isPU s xs -> begin
      match look (L.hd xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (L.tl xs) s
      | _ -> assert false
    end
  | ((App xs as x), y) when isPU s xs -> begin
      match look (L.hd xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (L.tl xs) s
      | _ -> assert false
    end
  | _ ->
    Format.eprintf "NOT A PU: %a = %a\n%!"
      (prf_data []) (Red.nf s (kool x)) (prf_data []) (Red.nf s (kool y));
    assert false (*fail "not a pattern unif"*)

(* ******************************** Main loop ******************************* *)

exception NoClause
type objective =
  [ `Atom of data * key
  | `Unify of data * data | `Custom of string * data | `Cut
  | `Delay of data * premise
  | `Resume of data * premise
  | `Unlock of data
  ]
type goal = int * objective * program * program * int
type dgoal = data * premise * int * program * annot_clause
type goals = goal list * dgoal list * program
type alternatives = (subst * goals) list
type continuation = premise * program *  alternatives
type step_outcome = subst * goal list * alternatives
type result = LP.goal * LP.data list * Subst.subst * LP.goal list * continuation

let cat_goals (a,b,p) (c,d) = a@c, b@d, p

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

let pr_cur_goal eh g lvl s fmt =
  match g with
  | `Atom (goal,_) ->
      Format.fprintf fmt "@[<hov 2>%a@ |- %a@]"
        prf_program (List.map (fun a,b,p -> a,b,Red.nf s p) eh)
        (prf_premise []) (apply_subst s goal)
  | `Unify(a,b) ->
      Format.fprintf fmt "%a = %a"
          (prf_data []) (apply_subst s a) (prf_data []) (apply_subst s b)
  | `Custom(name,a) ->
      Format.fprintf fmt "%s %a" name (prf_data []) (apply_subst s a)
  | `Cut -> Format.fprintf fmt "!"
  | `Delay (t,p) ->
       Format.fprintf fmt "delay %a %a"
         (prf_data []) t (prf_premise []) (Red.nf s p)
  | `Resume (t,p) -> Format.fprintf fmt "resume %a %a" (prf_data []) t (prf_premise []) (Red.nf s p)
  | `Unlock t -> Format.fprintf fmt "unlock %a" (prf_data []) t
let pr_cur_goals gls fmt s =
  Format.fprintf fmt "@[<hov 0>"; 
  iter_sep (fun fmt () -> Format.fprintf fmt ",@ ")
    (fun fmt (_,g,_,eh,l) -> pr_cur_goal eh g l s fmt) fmt gls;
  Format.fprintf fmt "@]" 

let custom_tab = ref []
let register_custom n f = custom_tab := ("$"^n,f) :: !custom_tab
let custom name t s d p =
  try List.assoc name !custom_tab t s d p
  with Not_found -> raise(Invalid_argument ("custom "^name))

let subst t hv =
  let t1 = mkApp(L.of_list (mkBin (List.length hv) t::List.rev hv)) in
(*   let t1 = Red.nf (Subst.empty 0) t1 in *)
  SPY "substituted premise/goal" (prf_data []) t1;
  t1

let add_cdepth b cdepth =
  List.map (fun p -> cdepth, (if b then key_of p else Flex), p)

let mkAtom t = `Atom(t, key_of t)

let whd_premise s p =
  let p = Red.nf s p in
  match look_premise p with
  | Pi (n,p) -> let p, s = Red.whd s p in mkPi n p, s
  | Sigma (n,p) -> let p, s = Red.whd s p in mkSigma n p, s 
  | _ -> p, s

let contextualize_premise ?(compute_key=false) depth s premise =
  let rec aux cdepth s eh p =
    let p, s = whd_premise s p in
    match look_premise p with
    | Atom t ->
        [cdepth, mkAtom t, add_cdepth compute_key cdepth eh], s
    | AtomBI (BIUnif(x,y)) ->
        [cdepth, `Unify(x,y), add_cdepth compute_key cdepth eh], s
    | AtomBI (BICustom(n,x)) ->
        [cdepth, `Custom(n,x), add_cdepth compute_key cdepth eh], s
    | AtomBI BICut ->
        [cdepth, `Cut, add_cdepth compute_key cdepth eh], s
    | Impl(ps,h) when isConj ps -> aux cdepth s (destConj ps @ eh) h
    | Impl(p,h) -> aux cdepth s (p :: eh) h
    | Pi(n,h) -> aux (cdepth+1) s eh (subst h (mkhv n (cdepth+1)))
    | Sigma(n,h) ->
        let ms, s = fresh_uv n cdepth s in
        aux cdepth s eh (subst h ms)
    | Conj l ->
        let ll, s = List.fold_right (fun p (acc,s) ->
          let l, s = aux cdepth s eh p in
          l::acc, s) (L.to_list l) ([],s) in
        List.flatten ll, s
    | Delay(t, p) -> [cdepth, `Delay (t,p), add_cdepth compute_key cdepth eh], s
    | Resume(t,p) -> [cdepth, `Resume(t,p), add_cdepth compute_key cdepth eh], s
  in
    aux depth s [] premise

let contextualize_hyp depth subst premise =
  match contextualize_premise depth subst premise with
  | [_,`Atom(hd,_),hyps], s -> hd, hyps, s
  | [], _ -> assert false
  | _ -> assert false

let contextualize_goal depth subst goal =
  contextualize_premise ~compute_key:true depth subst goal

let no_key_match k kc =
  match k, kc with
  | Key t1, Key t2 -> not(LP.equal t1 t2)
  | Key _, Flex -> true
  | Flex, _ -> false

let select p k goal depth (s as os) prog orig_eh lvl : step_outcome =
  let rec first = function
  | [] ->
      SPY "fail" (prf_data []) (apply_subst s goal);
      raise NoClause
  | (_,kc,clause) :: rest when no_key_match k kc -> first rest
  | (_,_,clause) :: rest ->
      try
        let hd, subgoals, (s as cs) = contextualize_hyp depth s clause in
        SPY "try" (prf_clause []) (Red.nf s clause);
        let s = unify goal hd s in
        SPY "selected" (prf_clause []) (Red.nf cs clause);
        SPY "sub" Subst.prf_subst s;
        let subgoals, s =
          List.fold_right (fun (d,_,p) (acc,s) ->
            let gl, s = contextualize_goal d s p in
            gl :: acc, s) subgoals ([],s) in
        let subgoals =
          List.map (fun (d,g,e) -> d,g,e@orig_eh@p,e@orig_eh,lvl+1)
            (List.flatten subgoals) in
        s, subgoals, [os,([depth,`Atom(goal,k),rest,orig_eh,lvl],[],p)]
      with UnifFail _ ->
        SPY "skipped" (prf_clause []) clause;
        first rest
  in
    first prog

let run1 p s ((depth,goal,prog,orig_eh,lvl) : goal) : step_outcome =
  match goal with
  | `Cut -> assert false
  | `Delay _ -> assert false
  | `Resume _ -> assert false
  | `Atom(t,k) ->
      let s, goals, alts = select p k t depth s prog orig_eh lvl in
      s, goals, alts
  | `Unlock t ->
      if not (Subst.is_tc t) then
        (Format.eprintf "not a tc: %a\n%!" (prf_data []) t; assert false);
      let h, s = Subst.fresh_uv 0 s in
      let hd = let rec uff t = match look t with
        | App xs -> uff (L.hd xs) | Con (n,_) -> n | _ -> assert false in
      uff t in
      Subst.set_body hd h s, [], []
  | `Unify(a,b) ->
      (try
        let s = unify a b s in
        SPY "sub" Subst.prf_subst s;
        s,[], []
      with UnifFail _ -> raise NoClause)
  | `Custom(name,a) ->
      (try
        let s = custom name a s depth prog in
        SPY "sub" Subst.prf_subst s;
        s,[], []
      with UnifFail _ -> raise NoClause)

let rec cut lvl = function
  | [] -> []
  | (_,((_,_,_,_,l)::_,_,_)) :: xs when l + 1 = lvl -> xs
  | _ :: xs -> cut lvl xs

let next_alt (alts : alternatives) pp =
  match alts with
  | [] -> raise NoClause
  | (s,(gs,dgs,p)) :: alts -> SPY "backtrack" pp s; s, gs, dgs, p, alts

let list_partmapfold f l a = 
  let rec aux xs ys a = function
  | [] -> List.rev xs, List.rev ys, a
  | z :: zs ->
     match f z a with
     | Some (z',a) -> aux (z'::xs) ys a zs
     | None -> aux xs (z::ys) a zs
  in
    aux [] [] a l

let flexible s t = let t, _s = Red.whd s t in
(*   Format.eprintf "flexible %a = not %b\n%!" (prf_data []) t (rigid (look t)); *)
  not (rigid (look t))

let goals_of_premise p clause depth eh lvl s =
  let gl, s = contextualize_goal depth s clause in
  List.map (fun (d,g,e) -> d,g,e@eh@p,e@eh,lvl+1) gl, s

let resume p s test lvl (dls : dgoal list) =
  list_partmapfold (fun (t,clause,depth,eh,to_purge) s ->
    if test t then None
    else
            (* FIXME: to_purge should be an id (int) *)
       let p = List.filter (fun x -> not(x = to_purge)) p in
       let gl, s = goals_of_premise p clause depth eh lvl s in
       SPY "will resume" (prf_premise []) (Red.nf s clause);
       SPY "hd" (prf_data []) (Red.nf s t);
       Some(gl,s)) dls s
         
let add_delay (t,a,depth,orig_prog as dl) s dls run = 
(*   let a = destAtom a in *)
  let rec aux = function
  | [] -> dl :: dls, s
(*
  | (t',a',depth',orig_prog') :: rest
    when LP.equal (Red.nf s t) (Red.nf s t') ->
      let a' = destAtom a' in
      let g = mkApp (L.of_list [mkCon "eq" 0; a; a']) in
      let is_funct =
        try let _ = run s ([max depth depth',`Atom(g,key_of g),orig_prog,orig_prog,0],[]) [] in true
        with NoClause -> false in
      if not is_funct then aux rest
      else assert false
*)
  | _ :: rest -> aux rest 
  in
    aux dls

let rec destFlexHd t =
  match look t with
  | Uv(i,_) -> i
  | App xs -> destFlexHd (L.hd xs)
  | _ -> assert false

let bubble_up s t p (eh : program) : annot_clause * subst =
  let k = key_of p in
  let p = mkImpl (mkConj (L.of_list (List.map (fun _,_,x -> x) eh))) p in
  let hvs = collect_hv_premise p in      
  let h, s = Subst.fresh_uv 0 s in
  let h_hvs = mkApp (L.of_list (h :: hvs)) in
(*
  Format.eprintf "h hvs = %a\n%!" (prf_data []) h_hvs;
  Format.eprintf "p = %a\n%!" (prf_data []) (Red.nf s p);
*)
  let i = destFlexHd t in
  let s = Subst.set_sub i (Subst.fresh_tc ()) s in
  let s = unify h_hvs p s in
  let abstracted =
    if List.length hvs = 0 then (Red.nf s h) else (mkSigma 0 (Red.nf s h)) in
  Format.eprintf "astratto %a\n%!" (prf_premise []) abstracted;
  (0, k, abstracted), s

let rec same_hd a b =
       SPY "same-hd hd1" (prf_data []) ( a);
       SPY "same-hd hd2" (prf_data []) ( b);

 match look a, look b with
 | Con _, Con _ -> LP.equal a b
 | App xs, App ys -> same_hd (L.hd xs) (L.hd ys)
 | _ -> false

let rec run op s ((gls,dls,p) : goals) (alts : alternatives) : subst * dgoal list * alternatives =
(*   SPY "status" (fun fmt -> Format.fprintf fmt "%d") (List.length dls); *)
  let s, gls, dls, p, alts =
    match gls with
    | [] -> s, [], dls, p, alts
    | (_,`Cut,_,_,lvl)::rest ->
       let alts = cut lvl alts in
       s, rest, dls, p, alts
    | (depth,`Resume(t,goal), _, eh,lvl) :: rest ->
         let resumed, dls, s =
           resume p s (fun t1 -> not(same_hd (Red.nf s t) (Red.nf s t1))) lvl dls in
         let resumed = List.flatten resumed in
         Format.eprintf "riesumati : %d\n%!" (List.length resumed);
         let gl, s = goals_of_premise p goal depth eh lvl s in
         let unlock = depth,`Unlock t,[],eh,lvl in
         s, unlock::gl@resumed@rest, dls, p, alts
    | (depth,(`Delay(t,goal) as go), _, eh,lvl) :: rest ->
       if true || flexible s t then
         try
           TRACE "delay" (pr_cur_goal eh go lvl s)
           let new_hyp, s = bubble_up s t goal eh in
           let dls = (t,goal,depth,eh,new_hyp) :: dls in
           s, List.map (fun (d,g,cp,eh,l) -> (* siblings are pristine *)
                d,g,eh@(new_hyp::p),eh,l) rest, dls, new_hyp :: p,
           alts
         with NoClause -> next_alt alts (pr_cur_goals gls)
       else
         let gl, s = goals_of_premise p goal depth eh lvl s in
         s, gl@rest, dls, p, alts
    | (_,go,hyps,eh,lvl as g)::rest ->
       try
         let hyps_nop =
           let nhyps = List.length hyps in let nop = List.length op in
           if nhyps <= nop then []
           else L.to_list (L.sub 0 (nhyps - nop) (L.of_list hyps)) in
         TRACE "run" (pr_cur_goal hyps_nop go lvl s)
         let s, subg, new_alts = run1 p s g in
         let resumed, dls', s = resume p s (fun t -> true || flexible s t) lvl dls in
         let resumed = List.flatten resumed in
         s, (resumed@subg@rest), dls', p,
           (List.map (fun (s,gs) -> s,cat_goals gs (rest,dls)) new_alts @ alts)
       with
       | NoClause -> next_alt alts (pr_cur_goals gls)
  in
  if gls = [] then s, dls, alts
  else run op s (gls,dls,p) alts

let prepare_initial_goal g =
  let s = empty 1 in
  match look_premise g with
  | Sigma(n,g) ->
      let ms, s = fresh_uv n 0 s in
      subst g ms, s
  | _ -> g, s

let apply_sub_hv_to_goal s g =
  mapi_premise (fun i t ->
    let v = L.init i (fun j -> mkDB(i-j)) in
    fst(Red.whd s (mkAppv (mkBin i t) v 0 (L.len v)))) 0 g

let return_current_result op s g dls alts =
  apply_sub_hv_to_goal (Subst.empty 0) g, collect_Uv_premise g, s,
  List.map (fun (_,g,_,_,_) -> apply_sub_hv_to_goal s g) dls,
  (g,op,alts)

let run_dls (p : program) (g : premise) =
  let g, s = prepare_initial_goal g in
  (*Format.eprintf "@[<hv2>goal:@ %a@]@\n%!" (prf_goal (ctx_of_hv hv)) g;*)
  let gls, s = contextualize_goal 0 s g in
  let s, dls, alts =
    run p s (List.map (fun (d,g,ep) -> (d,g,ep@p,ep,0)) gls, [], p) [] in
  return_current_result p s g dls alts

let next (g,op,alts) =
 let s,gls,dls,p,alts =
  next_alt alts (fun fmt _ -> Format.fprintf fmt "next solution") in
 (* from now on cut&paste from run_dls, the code need factorization *)
 let s, dls, alts = run op s (gls,dls,p) alts in
 return_current_result op s g dls alts

let run p g = let a,_,b,_,_ = run_dls p g in a, b

(* vim:set foldmethod=marker: *)
