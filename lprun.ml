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
    (prf_data []) (fst(Red.nf a s)) rel (prf_data []) (fst(Red.nf b s))

let rec rigid x = match x with
  | Uv _ -> false
  | App xs -> rigid (look (L.hd xs))
  | _ -> true

let eta n t =
  fixApp (L.init (n+1) (fun i -> if i = 0 then (lift n t) else mkDB (n+1-i)))

(* construction of bindings: ↓ is ^- and ⇑ is ^= *)
let cst_lower xs lvl =
  L.filter (fun x -> match look x with Con(_,l) -> l <= lvl | _ -> false) xs

let position_of l = let stop = L.len l in fun x s ->
  let x, s = Red.whd x s in
  let rec aux i s = function
    | [] -> fail "cannot occur"
    | y::ys -> 
        let y, s = Red.whd y s in
        if equal x y then mkDB (stop - i), s else aux (i+1) s ys
  in aux 0 s (L.to_list l)
  
let ($) f x = f x
let (^=) = cst_lower
let (^-) what where s = L.fold_map (position_of where) what s
let (^--) x v s = position_of v x s

let inter xs ys s =
  let ys, s = L.fold_map Red.whd ys s in
  L.filter_acc (fun x s ->
     let x, s = Red.whd x s in
     L.exists (LP.equal x) ys, s) xs s

(* builds: map (lift nbinders) args @ [DB nbinders ... DB 1] *)
let mk_al nbinders args =
  let nargs = L.len args in
  L.init (nbinders + nargs)
    (fun i ->
      if i < nargs then Red.lift nbinders (L.get i args)
      else mkDB (nargs + nbinders - i))

(* pattern unification fragment *)
let higher lvl = (); fun x ->
  match look x with Con(_,l) -> l > lvl | DB _ -> true | _ -> false

let last_isPU = ref (Subst.empty 0)

let isPU xs s = TRACE "isPU" (fun fmt -> prf_data [] fmt (mkApp xs))
  match look (L.hd xs) with
  | Uv (_,lvl) ->
      let args, s = L.fold_map Red.whd (L.tl xs) s in
      last_isPU := s;
      L.for_all (higher lvl) args && L.uniq LP.equal args
  | _ -> false

let rec bind x id depth lvl args t s =
  let t, s = whd t s in
  TRACE "bind" (print_unif_prob s (":= "^string_of_int depth^"↓") x t)
  match look t with
  | Bin(m,t) -> let t, s = bind x id (depth+m) lvl args t s in mkBin m t, s
  | Ext _ -> t, s
  | Con (_,l) when l <= lvl -> t, s
  | Con _ -> t ^-- mk_al depth args $ s (* XXX optimize *)
  (* the following 2 cases are: t ^-- mk_al depth args, s *) (* XXX CHECK *)
  | DB m when m <= depth -> t, s
  | DB m -> let t, s = mkDB (m-depth) ^-- args $ s in lift depth t, s
  | Seq(xs,tl) ->
      let xs, s = L.fold_map (bind x id depth lvl args) xs s in
      let tl, s = bind x id depth lvl args tl s in
      mkSeq xs tl, s
  | Nil -> t, s
  | App bs as t when rigid t ->
      let ss, s = L.fold_map (bind x id depth lvl args) bs s in
      mkApp ss, s
  | VApp (b,h,a) ->
      let h, s = bind x id depth lvl args h s in
      let a, s = bind x id depth lvl args a s in
      mkVApp b h a, s
  | (App _ | Uv _) as tmp -> (* pruning *)
      let bs = match tmp with
        | App bs -> bs | Uv _ -> L.singl t | _ -> assert false in
      match look (L.hd bs) with
      | (Bin _|Con _|DB _|Ext _|App _|Seq _|Nil|VApp _) -> assert false
      | Uv(j,l) when j <> id && l > lvl && isPU bs s ->
          let s = !last_isPU in
          SPY "prune-copied-meta" (prf_data []) (L.hd bs);
          let bs = L.tl bs in
          let nbs = L.len bs in
          let h, s = fresh_uv lvl s in
          let al = mk_al depth args in
          let cs = al ^= l in (* constants X = id,lvl can copy *)
          let ws, s = cs ^- al $ s in
          let zs, s = inter al bs s in (* XXX paper excludes #l-1, why? *)
          let vs, s = zs ^- al $ s in
          let us, s = zs ^- bs $ s in
          let nws, nvs, ncs, nus = L.len ws, L.len vs, L.len cs, L.len us in
          let vj = mkBin nbs (mkAppv h (L.append cs us) 0 (ncs + nus)) in
          let s = set_sub j vj s in
          let t = mkAppv h (L.append ws vs) 0 (nws+nvs) in
          SPY "prune-vj" (prf_data []) vj; SPY "prune-t" (prf_data[]) t;
          t, s
      | Uv(j,l) when j <> id ->
          SPY "prune-no-PU" (prf_data []) (L.hd bs);
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
          SPY "prune-vj" (prf_data []) vj; SPY "prune-t" (prf_data[]) t;
          t, s
      | Uv(j,_) when j = id -> fail "occur-check"
      | Uv _ -> assert false (*fail "ho-ho"*)

let keep xs ys s =
  let l1 = L.to_list xs in
  let l2 = L.to_list ys in
  let rec aux l1 l2 i s =
    match l1, l2 with
    | [], [] -> [], s
    | x::xs, y::ys ->
       let x, s = Red.nf x s in
       let y, s = Red.nf y s in
       if equal x y then let l, s = aux xs ys (i-1) s in mkDB i :: l, s
       else aux xs ys (i-1) s
    | _ -> Format.eprintf "ERROR: same meta, different #args\n%!"; assert false
  in
  let l, s = aux l1 l2 (L.len xs) s in
  L.of_list l, s

let rec simple_oc id lvl t s =
  match look t with
  | Uv(i,lvl') ->
      if i = id then fail "occur-check"
      else if lvl' >= lvl then
        let t', s = Red.whd t s in
        if t' == t then s else simple_oc id lvl t' s
      else s
  | Con _ | DB _ | Nil | Ext _ -> s
  | Bin(_,t) -> simple_oc id lvl t s
  | App l -> L.fold (simple_oc id lvl) l s
  | Seq(l,t) -> L.fold (simple_oc id lvl) l (simple_oc id lvl t s)
  | VApp(_,t1,t2) -> simple_oc id lvl t1 (simple_oc id lvl t2 s)

let mksubst ?depth x id lvl t args s =
  let nargs = L.len args in
  match look t with
  | App xs when equal (L.hd xs) (mkUv id lvl) && isPU xs s ->
      let s = !last_isPU in
      let xs, s = L.fold_map Red.whd (L.tl xs) s in
      if L.for_all2 equal xs args then s
      else
        let h_args, s = keep xs args s in
        if L.len h_args = nargs then s
        else
          let h, s = fresh_uv lvl s in
          set_sub id (mkBin nargs (mkApp (L.cons h h_args))) s
  | _ ->
     (* If a variable is at the deepest level, then the term can be copied
      * as it is *)
     if Some lvl = depth && L.len args = 0 then
       let s = simple_oc id lvl t s in
       set_sub id t s
     else
       let t, s = bind x id 0 lvl args t s in
       SPY "mksubst" (prf_data []) (mkBin nargs t);
       set_sub id (mkBin nargs t) s

let rec splay xs tl s =
  let tl, s = whd tl s in
  match look tl with
  | Uv _ | Nil -> xs, tl, s
  | Seq(ys,t) -> splay (L.append xs ys) t s
  | _ -> xs, tl, s

let destApp b t ot = match t with
  | App xs -> L.hd xs, if b == `Rev then L.rev (L.tl xs) else L.tl xs
  | Seq _ -> assert false
  | _ -> ot, L.empty

exception NOT_A_PU

let rec unify ?depth a b s = TRACE "unify" (print_unif_prob s "=" a b)
  let a, s =  whd a s in
  let b, s =  whd b s in
  match look a, look b with
  | Con _, Con _ | Ext _, Ext _ | DB _, DB _ | Nil, Nil ->
      if equal a b then s else fail "rigid"
  | VApp (b1,hd1,al1), VApp (b2,hd2,al2) ->
      if (b1 == `Rev && b2 == `Rev) || (b1 <> `Rev && b2 <> `Rev) then
        unify al1 al2 (unify hd1 hd2 s)
      else assert false

  | t, VApp(w,t1,t2) ->
     if w == `Flex && rigid t then fail "no-flex";
     if w == `Frozen && not(Subst.is_frozen a) then fail "no-tc";
     let hd, tl = destApp w t a in unify (mkSeq tl mkNil) t2 (unify hd t1 s)
  | VApp(w,t1,t2), t ->
     if w == `Flex && rigid t then fail "no-flex";
     if w == `Frozen && not(Subst.is_frozen b) then fail "no-tc";
     let hd, tl = destApp w t b in unify (mkSeq tl mkNil) t2 (unify hd t1 s)

  | Bin(nx,x), Bin(ny,y) when nx = ny -> unify x y s
  | Bin(nx,x), Bin(ny,y) when nx < ny -> unify (eta (ny-nx) x) y s
  | Bin(nx,x), Bin(ny,y) when nx > ny -> unify x (eta (nx-ny) y) s
  | ((Bin(nx,x), y) | (y, Bin(nx,x))) when rigid y ->unify x (eta nx (kool y)) s
  | Uv(i,_), Uv(j,_) when i = j -> s
  | x, y -> if rigid x && rigid y then unify_fo ?depth x y s else unify_ho ?depth x y s
and unify_fo ?depth x y s =
  match x, y with
  | App xs, App ys when L.len xs = L.len ys -> L.fold2 (unify ?depth) xs ys s
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
and unify_ho ?depth x y s =
  match x, y with
  | (((Uv (id,lvl) as x), y) | (y, (Uv (id,lvl) as x))) ->
      mksubst ?depth (kool x) id lvl (kool y) L.empty s
  | (y, (App xs as x)) when isPU xs s -> begin
      let s = !last_isPU in
      match look (L.hd xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (L.tl xs) s
      | _ -> assert false
    end
  | ((App xs as x), y) when isPU xs s -> begin
      let s = !last_isPU in
      match look (L.hd xs) with
      | Uv (id,lvl) -> mksubst (kool x) id lvl (kool y) (L.tl xs) s
      | _ -> assert false
    end
  | _ ->
    Format.eprintf
      "NOT A PU: %a = %a\n%!" (prf_data []) (kool x) (prf_data []) (kool y);
    raise NOT_A_PU (*fail "not a pattern unif"*)

(* ******************************** Main loop ******************************* *)

exception NoClause
type objective =
  [ `Atom of data * key
  | `Unify of data * data | `Custom of string * data | `Cut
  | `Delay of data * premise * data option
  | `Resume of data * premise
  | `Unlock of data
  ]
type context = data option list
type goal = context * objective * program * program * int
type dgoal = data * premise * context * program * int
type goals = goal list * dgoal list * program
type alternatives = (subst * goals) list
type continuation = premise * program *  alternatives
type step_outcome = subst * goal list * alternatives
type result =
 LP.goal * LP.data list * Subst.subst *
  (LP.goal * LP.program) list * continuation

let cat_goals (a,b,p) (c,d) = a@c, b@d, p

(* Important: when we move under a pi we put a constant in place of the
 * bound variable. This way hypothetical clauses do not need to be lifted
 * when we move under other pi binders *)
let mkhv_aux =
  let i = ref 0 in
  fun depth -> incr i; mkFreshCon ("𝓱"^subscript !i) depth
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

let pr_cur_goal op (_,g,hyps,_,lvl) s fmt =
  let eh = (* XXX This is inprecise, hypotheticals should have a special id *)
    let nhyps = List.length hyps in let nop = List.length op in
    if nhyps <= nop then []
    else L.to_list (L.sub 0 (nhyps - nop) (L.of_list hyps)) in
  match g with
  | `Atom (g,_) when !Trace.dverbose ->
      Format.fprintf fmt "@[<hv 0>%a@ |- %a@]"
        (prf_program ~compact:true)
            (List.map (fun a,b,p,n -> a,b,fst(Red.nf p s),n) eh)
        (prf_premise []) (fst(Red.nf g s))
  | `Atom (g,_) ->
      Format.fprintf fmt "@[<hv 0>|- %a@]" (prf_premise []) (fst(Red.nf g s))
  | `Unify(a,b) ->
      Format.fprintf fmt "%a = %a"
          (prf_data []) (fst(Red.nf a s)) (prf_data []) (fst(Red.nf b s))
  | `Custom(name,a) ->
      Format.fprintf fmt "%s %a" name (prf_data []) (fst(Red.nf a s))
  | `Cut -> Format.fprintf fmt "!"
  | `Delay (t,p,None) ->
       Format.fprintf fmt "delay %a %a"
         (prf_data []) (fst(Red.nf t s)) (prf_premise []) (fst(Red.nf p s))
  | `Delay (t,p,Some fl) ->
       Format.fprintf fmt "delay %a %a tabulate %a"
         (prf_data []) (fst(Red.nf t s)) (prf_premise []) (fst(Red.nf p s))
         (prf_data []) fl
  | `Resume (t,p) ->
       Format.fprintf fmt "resume %a %a" (prf_data []) t
         (prf_premise []) (fst(Red.nf p s))
  | `Unlock t ->
       Format.fprintf fmt "@[<hv 0>unlock %a@]" (prf_data []) (fst(Red.nf t s))

let pr_cur_goals op gls fmt s =
  Format.fprintf fmt "@[<hov 0>"; 
  iter_sep (fun fmt () -> Format.fprintf fmt ",@ ")
    (fun fmt g -> pr_cur_goal op g s fmt) fmt gls;
  Format.fprintf fmt "@]" 

let custom_predicate_tab = ref []
let register_custom_predicate n f =
  custom_predicate_tab := ("$"^n,f) :: !custom_predicate_tab
let is_custom_predicate name =
  List.mem_assoc name !custom_predicate_tab
let custom_predicate name =
  try List.assoc name !custom_predicate_tab
  with Not_found -> raise(Invalid_argument ("custom_predicate "^name))
let custom_ctrl_op_tab = ref []
let register_custom_control_operator n f =
  custom_ctrl_op_tab := ("$"^n,f) :: !custom_ctrl_op_tab
let is_custom_ctrl_op name =
  List.mem_assoc name !custom_ctrl_op_tab
let custom_ctrl_op name =
  try List.assoc name !custom_ctrl_op_tab
  with Not_found -> raise(Invalid_argument ("custom_ctrl_op "^name))

let subst t hv =
  let t1 = mkApp(L.of_list (mkBin (List.length hv) t::List.rev hv)) in
(*   let t1 = Red.nf (Subst.empty 0) t1 in *)
  SPY "substituted premise/goal" (prf_data []) t1;
  t1

let add_ctx_key_name b ctx l =
  List.map (fun p -> ctx, (if b then key_of p else Flex), p, CN.fresh ()) l

let mkAtom t = `Atom(t, key_of t)

let whd_premise s p =
  let p, s = Red.whd p s in
  match look_premise p with
  | Pi (annot,p) -> let p, s = Red.whd p s in mkPi1 annot p, s
  | Sigma p -> let p, s = Red.whd p s in mkSigma1 p, s 
  | _ -> p, s

let contextualize_premise ?(compute_key=false) ctx s premise =
  let rec aux ctx s eh p =
    let p, s = whd_premise s p in
    match look_premise p with
    | Atom t ->
        [ctx, mkAtom t, add_ctx_key_name compute_key ctx eh], s
    | AtomBI (BIUnif(x,y)) ->
        [ctx, `Unify(x,y), add_ctx_key_name compute_key ctx eh], s
    | AtomBI (BICustom(n,x)) ->
        [ctx, `Custom(n,x), add_ctx_key_name compute_key ctx eh], s
    | AtomBI BICut ->
        [ctx, `Cut, add_ctx_key_name compute_key ctx eh], s
    | Impl(ps,h) when isConj ps -> aux ctx s (destConj ps @ eh) h
    | Impl(p,h) -> aux ctx s (p :: eh) h
    | Pi(annot,h) ->
        let hv = mkhv 1 (List.length ctx+1) in
        let ctx_item = match annot with
          | Some t -> Some (mkSeq (L.of_list (hv@[t])) mkNil)
          | None -> None in
        aux (ctx_item :: ctx) s eh (subst h hv)
    | Sigma h ->
        let ms, s = fresh_uv 1 (List.length ctx) s in
        aux ctx s eh (subst h ms)
    | Conj l ->
        let ll, s = List.fold_right (fun p (acc,s) ->
          let l, s = aux ctx s eh p in
          l::acc, s) (L.to_list l) ([],s) in
        List.flatten ll, s
    | Delay(t, p, fl) ->
        [ctx, `Delay (t,p,fl), add_ctx_key_name compute_key ctx eh], s
    | Resume(t,p) -> [ctx, `Resume(t,p), add_ctx_key_name compute_key ctx eh], s
  in
    aux ctx s [] premise

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

let select p k goal ctx (s as os) prog orig_eh lvl : step_outcome =
  let rec first = function
  | [] ->
      SPY "fail" (prf_data []) (apply_subst s goal);
      raise NoClause
  | (_,kc,clause,_) :: rest when no_key_match k kc -> first rest
  | (_,_,clause,_) :: rest ->
      try
        let hd, subgoals, (s as cs) = contextualize_hyp ctx s clause in
        SPY "try" (prf_clause []) (fst(Red.nf clause s));
        let s = unify ~depth:(List.length ctx) goal hd s in
        SPY "selected" (prf_clause []) (fst(Red.nf clause cs));
        SPY "sub" Subst.prf_subst s;
        let subgoals, s =
          List.fold_right (fun (d,_,p,_) (acc,s) ->
            let gl, s = contextualize_goal d s p in
            gl :: acc, s) subgoals ([],s) in
        let subgoals =
          List.map (fun (d,g,e) -> d,g,e@orig_eh@p,e@orig_eh,lvl+1)
            (List.flatten subgoals) in
        s, subgoals, [os,([ctx,`Atom(goal,k),rest,orig_eh,lvl],[],p)]
      with UnifFail _ ->
        SPY "skipped" (prf_clause []) clause;
        first rest
  in
    first prog

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

let flexible t = not (rigid (look t))

let goals_of_premise p clause depth eh lvl s =
  let gl, s = contextualize_goal depth s clause in
  List.map (fun (d,g,e) -> d,g,e@eh@p,e@eh,lvl+1) gl, s

let resume p s test lvl (dls : dgoal list) =
  list_partmapfold (fun (t,clause,depth,eh,_) s ->
    if test t then None
    else
       let gl, s = goals_of_premise p clause depth eh lvl s in
       SPY "will resume" (prf_premise []) (fst(Red.nf clause s));
       SPY "hd" (prf_data []) (fst(Red.nf t s));
       Some((gl,t),s)) dls s
         
let add_delay (t,a,depth,orig_prog as dl) s dls run = 
  let rec aux = function
  | [] -> dl :: dls, s
  | _ :: rest -> aux rest 
  in
    aux dls

let rec destFlexFrozenHd t l =
  match look t with
  | Uv(i,lvl) -> `Flex(i, lvl, l)
  | Con(_,lvl) when lvl < 0 -> `Frozen (lvl, l)
  | App xs -> destFlexFrozenHd (L.hd xs) (L.tl xs)
  | _ -> assert false

let hv_lvl_leq lvl t = match look t with
  | Con(_,l) -> l <= lvl
  | _ -> false

let rec uniq = function
  | ([] | [_]) as l -> l
  | x :: y :: l when LP.equal x y -> uniq (y :: l)
  | x :: l -> x :: uniq l

let rigid_key_match k1 k2 =
  match k1,k2 with Key a, Key b -> LP.equal a b | _ -> false

let is_cut x = match look_premise x with AtomBI BICut -> true | _ -> false

let freeze s t p filter =
  let t, s = Red.nf t s in
  let p, s = Red.nf p s in
  let filter, s =
    match filter with
    | None -> None, s
    | Some f -> let f, s = Red.nf f s in Some f, s in
  match destFlexFrozenHd t L.empty, filter with
  | `Frozen _, _ -> s
  | `Flex(i, lvl, args), None ->
    let ice, s = Subst.freeze_uv i s in
    let hvs = L.of_list (collect_hv p) in
    let ice_args = L.filter (fun h -> not(L.exists (LP.equal h) args)) hvs in
    Subst.set_sub i (mkApp (L.cons ice ice_args)) s
  | `Flex(i, lvl, args), Some l ->
    let ice, s = Subst.freeze_uv i s in
    let hvs = L.of_list (collect_hv l) in
    assert(L.for_all (fun h ->
      hv_lvl_leq lvl h || L.exists (LP.equal h) args) hvs);
    let ice_args, s =
      L.fold_map (fun h s ->
        try h ^-- args $ s with UnifFail _ -> h,s) hvs s in
    let res = mkBin (L.len args) (mkApp (L.cons ice ice_args)) in
    Subst.set_sub i res s

let not_same_hd s a b =
 let rec aux a b =
   let a, _ = Red.whd a s in
   let b, _ = Red.whd b s in
   match look a, look b with
   | Con _, Con _ -> not (LP.equal a b)
   | App xs, _ -> aux (L.hd xs) b
   | _, App ys -> aux a (L.hd ys)
   | _ -> true
 in aux a b

let mk_prtg str d l = d, `Custom("$print",mkExt(mkString str)), [], [], l

let not_in to_purge l =
  List.filter (fun x -> not(List.exists (eq_clause x) to_purge)) l

let sort_hyps (d,g,p,eh,lvl) = (d,g,List.sort cmp_clause p,eh,lvl)

let rec run op s ((gls,dls,p as goals) : goals) (alts : alternatives)
: subst * dgoal list * alternatives
=
  let s, gls, dls, p, alts =
    match gls with
    | [] -> s, [], dls, p, alts
    | (_,`Cut,_,_,lvl)::rest ->
        let alts = cut lvl alts in
        s, rest, dls, p, alts
    | (_,`Unlock t,_,_,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        let t, s = Red.whd t s in
        if not (Subst.is_frozen t) then
          (Format.eprintf "not frozen: %a\n%!" (prf_data []) t; assert false);
(*         Format.eprintf "ASSIGN META: %a\n%!" (prf_data []) t; *)
        let h, s = Subst.fresh_uv 0 s in
        let hd = let rec uff t = match look t with
          | App xs -> uff (L.hd xs) | Con (_,lvl) -> lvl | _ -> assert false in
        uff t in
        let rest = List.map (fun (d,g,cp,eh,l) -> d,g,cp,eh,l) rest in
        Subst.set_sub_con hd h s, rest, dls, p, alts
    | (depth,`Resume(t,goal), _, eh,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        let resumed, dls, s = resume p s (not_same_hd s t) lvl dls in
        let resumed, keys = List.split resumed in
        let resumed = List.flatten resumed in
        assert(List.for_all (equal (List.hd keys)) keys);
        let unlock = depth, `Unlock (List.hd keys), [], [], lvl+1 in
        let extra_hyps, s = contextualize_goal depth s goal in
        let extra_hyps = List.map
          (function (_,`Atom (g,k),[]) -> depth, k, g, CN.fresh ()
                    | _ -> assert false)
          extra_hyps in
        let first_resumed, rest_resumed = List.hd resumed, List.tl resumed in
        let first_resumed =
          match first_resumed with (d,g,pr,eh,lvl) ->
            (d,g,extra_hyps@pr,extra_hyps@eh,lvl) in
        s, unlock::(*gl@*)first_resumed :: rest_resumed@rest, dls, p, alts
    | (depth,`Delay(t,goal,fl), _, eh,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        let t, s = Red.whd t s in
        if Subst.is_frozen t then
          try
            TRACE "delay more" (pr_cur_goal op g s)
            SPY "key" (prf_data []) (fst(Red.nf t s));
            let dls = dls @ [t,goal,depth,eh,lvl] in
            s, rest, dls, p, alts
          with NoClause -> next_alt alts (pr_cur_goals op gls)
        else if flexible t then
          try
            TRACE "delay" (pr_cur_goal op g s)
            let s = freeze s t goal fl in
            SPY "key" (prf_data []) (fst(Red.nf t s));
            let dls = (t,goal,depth,eh,lvl) :: dls in
            s, rest, dls, p, alts
          with NoClause -> next_alt alts (pr_cur_goals op gls)
        else
          let gl, s = goals_of_premise p goal depth eh lvl s in
          s, gl@rest, dls, p, alts
    | (depth,`Atom(t,k),hyps,eh,lvl as g)::rest ->
        (try
          TRACE ~depth:lvl "run" (pr_cur_goal op g s)
          let s, subg, new_alts = select p k t depth s hyps eh lvl in
          let subg = List.map sort_hyps subg in
          s, subg@rest, dls, p,
            (List.map (fun (s,gs) -> s,cat_goals gs (rest,dls)) new_alts @ alts)
        with NoClause -> next_alt alts (pr_cur_goals op gls))
    | (depth,`Unify(a,b),hyps,eh,lvl as g)::rest ->
        (try
          TRACE ~depth:lvl "run" (pr_cur_goal op g s)
          let s = unify a b s in
          SPY "sub" Subst.prf_subst s;
          s, rest, dls, p, alts
        with UnifFail _ -> next_alt alts (pr_cur_goals op gls))
    | (depth,`Custom(name,a),hyps,eh,lvl as g)::rest ->
        if is_custom_predicate name then
          try
            TRACE ~depth:lvl "run" (pr_cur_goal op g s)
            let s = custom_predicate name a s in
            SPY "sub" Subst.prf_subst s;
            s, rest, dls, p, alts
          with UnifFail _ | NoClause -> next_alt alts (pr_cur_goals op gls)
        else if is_custom_ctrl_op name then
          try
            let s, (gls, dls, p), alts = custom_ctrl_op name a s goals alts in
            s, gls, dls, p, alts
          with UnifFail _ -> next_alt alts (pr_cur_goals op gls)
        else raise (Invalid_argument ("no custom named " ^ name))
  in
  if gls == [] then s, dls, alts
  else run op s (gls,dls,p) alts

let prepare_initial_goal g =
  let s = empty 1 in
  match look_premise g with
  | Sigma g ->
      let ms, s = fresh_uv 1 0 s in
      subst g ms, s
  | _ -> g, s

let apply_sub_hv_to_goal s g =
  mapi_premise (fun i t ->
    let v = L.init i (fun j -> mkDB(i-j)) in
    fst(Red.whd (mkAppv (mkBin i t) v 0 (L.len v)) s)) 0 g

let return_current_result op s g dls alts =
  apply_sub_hv_to_goal (Subst.empty 0) g, collect_Uv_premise g, s,
  List.map (fun (_,g,_,eh,_) ->
   apply_sub_hv_to_goal s g,
   List.map (fun (i,k,c,u) -> i,k,apply_sub_hv_to_goal s c,u) eh) dls,
  (g,op,alts)

let run_dls (p : program) (g : premise) =
  let g, s = prepare_initial_goal g in
  let gls, s = contextualize_goal [] s g in
  let s, dls, alts =
    run p s (List.map (fun (d,g,ep) -> (d,g,ep@p,ep,0)) gls, [], p) [] in
  return_current_result p s g dls alts

let next (g,op,alts) =
 let s,gls,dls,p,alts =
  next_alt alts (fun fmt _ -> Format.fprintf fmt "next solution") in
 let s, dls, alts = run op s (gls,dls,p) alts in
 return_current_result op s g dls alts

let run p g = let a,_,b,_,_ = run_dls p g in a, b

(* vim:set foldmethod=marker: *)
