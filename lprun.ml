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
  | `Delay of data * premise
  | `Resume of data * premise
  | `Unlock of data * annot_clause list
  ]
type goal = int * objective * program * program * int
type dgoal = data * premise * int * program * int * annot_clause
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
  | `Delay (t,p) ->
       Format.fprintf fmt "delay %a %a"
         (prf_data []) (fst(Red.nf t s)) (prf_premise []) (fst(Red.nf p s))
  | `Resume (t,p) ->
       Format.fprintf fmt "resume %a %a" (prf_data []) t
         (prf_premise []) (fst(Red.nf p s))
  | `Unlock (t,ps) ->
       Format.fprintf fmt "@[<hv 0>unlock %a@ purge %a@]"
         (prf_data []) (fst(Red.nf t s)) (prf_program ~compact:true) ps

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
let custom_control_operator_tab = ref []
let register_custom_control_operator n f =
  custom_control_operator_tab := ("$"^n,f) :: !custom_control_operator_tab
let is_custom_control_operator name =
  List.mem_assoc name !custom_control_operator_tab
let custom_control_operator name =
  try List.assoc name !custom_control_operator_tab
  with Not_found -> raise(Invalid_argument ("custom_control_operator "^name))

let subst t hv =
  let t1 = mkApp(L.of_list (mkBin (List.length hv) t::List.rev hv)) in
(*   let t1 = Red.nf (Subst.empty 0) t1 in *)
  SPY "substituted premise/goal" (prf_data []) t1;
  t1

let add_cdepth b cdepth =
  List.map (fun p -> cdepth, (if b then key_of p else Flex), p, CN.fresh ())

let mkAtom t = `Atom(t, key_of t)

let whd_premise s p =
  let p, s = Red.whd p s in
  match look_premise p with
  | Pi (n,p) -> let p, s = Red.whd p s in mkPi n p, s
  | Sigma (n,p) -> let p, s = Red.whd p s in mkSigma n p, s 
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
  | (_,kc,clause,_) :: rest when no_key_match k kc -> first rest
  | (_,_,clause,_) :: rest ->
      try
        let hd, subgoals, (s as cs) = contextualize_hyp depth s clause in
        SPY "try" (prf_clause []) (fst(Red.nf clause s));
        let s = unify ~depth goal hd s in
        SPY "selected" (prf_clause []) (fst(Red.nf clause cs));
        SPY "sub" Subst.prf_subst s;
        let subgoals, s =
          List.fold_right (fun (d,_,p,_) (acc,s) ->
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

let flexible s t = let t, _s = Red.whd t s in not (rigid (look t))

let goals_of_premise p clause depth eh lvl s =
  let gl, s = contextualize_goal depth s clause in
  List.map (fun (d,g,e) -> d,g,e@eh@p,e@eh,lvl+1) gl, s

let resume p s test (dls : dgoal list) =
  list_partmapfold (fun (t,clause,depth,eh,lvl,to_purge) s ->
    if test t then None
    else
            (* FIXME: to_purge should be an id (int) *)
       let p = List.filter (fun x -> not(eq_clause x to_purge)) p in
       let gl, s = goals_of_premise p clause depth eh lvl s in
       SPY "will resume" (prf_premise []) (fst(Red.nf clause s));
       SPY "hd" (prf_data []) (fst(Red.nf t s));
       Some((gl,to_purge,t),s)) dls s
         
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

let rec destFlexHd t l =
  match look t with
  | Uv(i,lvl) -> i, lvl, l
  | App xs -> destFlexHd (L.hd xs) (L.to_list (L.tl xs))
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

let bubble_up s t p (eh : program) : annot_clause * subst =
  let t, s = Red.nf t s in
  let p, s = Red.nf p s in
  let k = key_of p in
  let i, lvl, ht = destFlexHd t [] in
  let eh = L.of_list eh in
  let k_of = key_of (mkCon "of" 0) in
  let eh = L.filter (fun _,k1,_,_ -> rigid_key_match k_of k1) eh in
  let eh, s = L.fold_map (fun (_,_,p,_) s -> Red.nf p s) eh s in
  let eh = List.map
    (fun x -> match look_premise x with Impl(x,p) when is_cut x -> p | _ -> x)
    (L.to_list eh) in
  let hvs_p = collect_hv_premise p in
  let hvs = hvs_p :: List.map collect_hv_premise eh in
  let hvs = uniq (List.sort LP.compare (List.flatten hvs)) in
  let hvs = List.filter
    (fun h -> hv_lvl_leq lvl h || List.exists (LP.equal h) hvs_p) hvs in
(*   Format.eprintf "hvs1=%a\n%!" (prf_data []) (mkSeq (L.of_list hvs) mkNil); *)
  let hyp = mkImpl (mkConj (L.of_list
    ((List.filter (fun x ->
        let hvsx = collect_hv_premise x in
        List.for_all (fun h -> List.exists (LP.equal h) hvs) hvsx) eh)
    @ [mkAtomBiCut]))) p in
  let hvs = L.of_list (collect_hv_premise hyp) in
  let h, s = Subst.fresh_uv 0 s in
  let h_hvs = mkApp (L.cons h hvs) in
(*
  Format.eprintf "h hvs = %a\n%!" (prf_data []) h_hvs;
  Format.eprintf "hyp = %a\n%!" (prf_data []) hyp;
*)
  let ice, s = Subst.freeze_uv i s in
  let ice_args = L.filter (fun h -> not(List.exists (LP.equal h) ht)) hvs in
  let s = Subst.set_sub i (mkApp (L.cons ice ice_args)) s in
  let s =
    try unify h_hvs hyp s
    with UnifFail err -> 
       Format.eprintf "*** bubble up: delif fails: %s@\nproblem: @[%a@]\n%!"
         (Lazy.force err) (fun fmt b -> print_unif_prob s "=" h_hvs b fmt) hyp;
       raise NoClause
  in
  let abstracted, s =
    if L.len hvs = 0 then Red.nf h s
    else let h, s = Red.nf h s in mkSigma 0 h, s in
  SPY "tabulated" (prf_clause []) abstracted;
  (0, k, abstracted,CN.fresh()), s

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

let rec list_split3 = function
  | [] -> [], [], []
  | (a,b,c) :: tl ->
     let tl1, tl2, tl3 = list_split3 tl in a::tl1, b::tl2, c::tl3

let rec run op s ((gls,dls,p as goals) : goals) (alts : alternatives)
: subst * dgoal list * alternatives
=
  let s, gls, dls, p, alts =
    match gls with
    | [] -> s, [], dls, p, alts
    | (_,`Cut,_,_,lvl)::rest ->
        let alts = cut lvl alts in
        s, rest, dls, p, alts
    | (_,`Unlock (t,to_purge),_,_,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        let t, s = Red.whd t s in
        if not (Subst.is_frozen t) then
          (Format.eprintf "not frozen: %a\n%!" (prf_data []) t; assert false);
(*         Format.eprintf "ASSIGN META: %a\n%!" (prf_data []) t; *)
        let h, s = Subst.fresh_uv 0 s in
        let hd = let rec uff t = match look t with
          | App xs -> uff (L.hd xs) | Con (_,lvl) -> lvl | _ -> assert false in
        uff t in
        let rest = List.map (fun (d,g,cp,eh,l) ->
          let cp = not_in to_purge cp in
          d,g,cp,eh,l) rest in
        let p = not_in to_purge p in
        Subst.set_sub_con hd h s, rest, dls, p, alts
    | (depth,`Resume(t,goal), _, eh,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        let resumed, dls, s = resume p s (not_same_hd s t) dls in
        let resumed, to_purge, keys = list_split3 resumed in
        let resumed =
          (*let start = mk_prtg "<<resume\n" depth lvl in
          let stop = mk_prtg "resume>>\n" depth lvl in*)
          (*start ::*) List.flatten resumed (*@ [stop]*) in
        let unlock = depth, `Unlock (List.hd keys, to_purge), [], [], lvl in
        let extra_hyps, s = contextualize_goal depth s goal in
        let extra_hyps = List.map
          (function (_,`Atom (g,k),[]) -> depth, k, g, CN.fresh ()
                    | _ -> assert false)
          extra_hyps in
        let resumed =
          List.map (fun (d,g,pr,eh,lvl) ->
            (d,g,extra_hyps@pr,extra_hyps@eh,lvl))
          resumed in
        s, unlock::(*gl@*)resumed@rest, dls, p, alts
    | (depth,`Delay(t,goal), _, eh,lvl as g) :: rest ->
        TRACE ~depth:lvl "run" (pr_cur_goal op g s)
        if true || flexible s t then
          try
            TRACE "delay" (pr_cur_goal op g s)
            let new_hyp, s = bubble_up s t goal eh in
            SPY "key" (prf_data []) (fst(Red.nf t s));
            let dls = (t,goal,depth,eh,lvl,new_hyp) :: dls in
            s, List.map (fun (d,g,cp,eh,l) -> (* siblings are pristine *)
                    d,g,eh@p@[new_hyp],eh(*@[new_hyp]*),l) rest, dls, p @ [new_hyp],
            alts
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
        else if is_custom_control_operator name then
           let s,(gls,dls,p),alts = custom_control_operator name a s goals alts in
           s, gls, dls, p, alts
        else raise (Invalid_argument ("no custom named " ^ name))
  in
  if gls == [] then s, dls, alts
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
    fst(Red.whd (mkAppv (mkBin i t) v 0 (L.len v)) s)) 0 g

let return_current_result op s g dls alts =
  apply_sub_hv_to_goal (Subst.empty 0) g, collect_Uv_premise g, s,
  List.map (fun (_,g,_,eh,_,_) ->
   apply_sub_hv_to_goal s g,
   List.map (fun (i,k,c,u) -> i,k,apply_sub_hv_to_goal s c,u) eh) dls,
  (g,op,alts)

let run_dls (p : program) (g : premise) =
  let g, s = prepare_initial_goal g in
  let gls, s = contextualize_goal 0 s g in
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
