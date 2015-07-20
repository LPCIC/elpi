(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Utils : sig

  val pplist : ?max:int -> ?boxed:bool ->
    (Format.formatter -> 'a -> unit) -> string ->
      Format.formatter -> 'a list -> unit

  val smart_map : ('a -> 'a) -> 'a list -> 'a list

  (* tail rec when the two lists have len 1; raises no exception. *)
  val for_all2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

  (* A regular error *)
  val error : string -> 'a

  (* An invariant is broken, i.e. a bug *)
  val anomaly : string -> 'a
  
  (* If we type check the program, then these are anomalies *)
  val type_error : string -> 'a

end = struct (* {{{ *)

let pplist ?(max=max_int) ?(boxed=false) ppelem sep f l =
 if l <> [] then begin
  if boxed then Format.fprintf f "@[<hov 1>";
  let args,last = match List.rev l with
    [] -> assert false;
  | head::tail -> List.rev tail,head in
  List.iteri (fun i x -> if i = max + 1 then Format.fprintf f "..."
                         else if i > max then ()
                         else Format.fprintf f "%a%s@ " ppelem x sep) args;
  Format.fprintf f "%a" ppelem last;
  if boxed then Format.fprintf f "@]"
 end
;;

let rec smart_map f =
 function
    [] -> []
  | (hd::tl) as l ->
     let hd' = f hd in
     let tl' = smart_map f tl in
     if hd==hd' && tl==tl' then l else hd'::tl'
;;

let rec for_all2 p l1 l2 =
  match (l1, l2) with
  | ([], []) -> true
  | ([a1], [a2]) -> p a1 a2
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> false
;;

let error s =
  Printf.eprintf "Fatal error: %s\n%!" s;
  exit 1
let anomaly s =
  Printf.eprintf "Anomaly: %s\n%!" s;
  exit 2
let type_error = error

end (* }}} *)
open Utils

module F = Parser.ASTFuncS

(* TODOS:
   - There are a few TODOs with different implementative choices to
     be benchmarked *)

(* Invariant: a Heap term never points to a Query term *)
type constant = int (* De Brujin levels *)
type term =
  (* Pure terms *)
  | Const of constant
  | Lam of term
  | App of constant * term * term list
  (* Clause terms: unif variables used in clauses *)
  | Arg of (*id:*)int * (*argsno:*)int
  | AppArg of (*id*)int * term list
  (* Heap terms: unif variables in the query *)
  | UVar of term ref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term ref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | String of F.t
  | Int of int
  | Float of float

module Constants : sig

  val funct_of_ast : F.t -> constant * term
  val constant_of_dbl : constant -> term
  val string_of_constant : constant -> string
 
  (* To keep the type of terms small, we use special constants for ! = pi.. *)
  val cutc   : term
  val truec  : term
  val andc   : constant
  val orc    : constant
  val implc  : constant
  val rimplc  : constant
  val pic    : constant
  val sigmac : constant
  val eqc    : constant
  val isc    : constant

  (* Value for unassigned UVar/Arg *)
  val dummy  : term

end = struct (* {{{ *)

(* Hash re-consing :-( *)
let funct_of_ast, constant_of_dbl, string_of_constant =
 let h = Hashtbl.create 37 in
 let h' = Hashtbl.create 37 in
 let h'' = Hashtbl.create 17 in
 let fresh = ref 0 in
 (function x ->
  try Hashtbl.find h x
  with Not_found ->
   decr fresh;
   let n = !fresh in
   let xx = Const n in
   let p = n,xx in
   Hashtbl.add h' n (F.pp x);
   Hashtbl.add h x p; p),
 (function x ->
  try Hashtbl.find h'' x
  with Not_found ->
   let xx = Const x in
   Hashtbl.add h' x ("x" ^ string_of_int x);
   Hashtbl.add h'' x xx; xx),
 (function n ->
   try Hashtbl.find h' n
   with Not_found -> string_of_int n)

let cutc = snd (funct_of_ast F.cutf)
let truec = snd (funct_of_ast F.truef)
let andc = fst (funct_of_ast F.andf)
let orc = fst (funct_of_ast F.orf)
let implc = fst (funct_of_ast F.implf)
let rimplc = fst (funct_of_ast F.rimplf)
let pic = fst (funct_of_ast F.pif)
let sigmac = fst (funct_of_ast F.sigmaf)
let eqc = fst (funct_of_ast F.eqf)
let isc = fst (funct_of_ast F.isf)

let rec dummy = App (-9999,dummy,[])

end (* }}} *)
open Constants


(* mkinterval d n 0 = [d; ...; d+n-1] *)
let rec mkinterval depth argsno n =
 if n = argsno then [] else (n+depth)::mkinterval depth argsno (n+1)
;;

module Pp : sig
 
  (* Low level printing *)
  val ppterm :
    constant -> string list ->
    constant -> term array ->
      Format.formatter -> term -> unit

  (* For user consumption *)
  val uppterm :
    constant -> string list ->
    constant -> term array ->
      Format.formatter -> term -> unit

  val pp_FOprolog :
    string list -> term array -> Format.formatter -> term -> unit

  val do_deref : (from:int -> to_:int -> int -> term -> term) ref
  val do_app_deref : (from:int -> to_:int -> term list -> term -> term) ref

end = struct (* {{{ *)

let do_deref = ref (fun ~from ~to_ _ _ -> assert false);;
let do_app_deref = ref (fun ~from ~to_ _ _ -> assert false);;
let m = ref [];;
let n = ref 0;;

let xppterm ~nice depth0 names argsdepth env f t =
  let pp_app f pphd pparg (hd,args) =
   if args = [] then pphd f hd
   else
    Format.fprintf f "(@[<hov 1>%a@ %a@])" pphd hd (pplist pparg "") args in
  let ppconstant f c = Format.fprintf f "%s" (string_of_constant c) in
  let rec pp_uvar depth vardepth args f r =
   if !r == dummy then begin
    let s =
     try List.assq r !m
     with Not_found ->
      let s =
       "X" ^ string_of_int !n ^ if vardepth=0 then "" else "^" ^ string_of_int vardepth
      in
      incr n;
      m := (r,s)::!m;
      s
    in
     Format.fprintf f "%s" s 
   (* TODO: (potential?) bug here, the variable is not lifted
      from origdepth (currently not even passed to the function)
      to depth (not passed as well) *)
   end else if nice then begin
    aux depth f (!do_deref ~from:vardepth ~to_:depth args !r)
   end else Format.fprintf f "<%a>_%d" (aux vardepth) !r vardepth
  and pp_arg depth f n =
   let name= try List.nth names n with Failure _ -> "A" ^ string_of_int n in
   if try env.(n) == dummy with Invalid_argument _ -> true then
    Format.fprintf f "%s" name
   (* TODO: (potential?) bug here, the argument is not lifted
      from g_depth (currently not even passed to the function)
      to depth (not passed as well) *)
   else if nice then aux depth f (!do_deref ~from:argsdepth ~to_:depth 0 env.(n))
   else Format.fprintf f "≪%a≫ " (aux argsdepth) env.(n)
  and aux depth f = function
      App (hd,x,xs) ->
        if hd==eqc then
         Format.fprintf f "@[<hov 1>%a@ =@ %a@]" (aux depth) x (aux depth) (List.hd xs)
        else if hd==orc then
         Format.fprintf f "(%a)" (pplist (aux depth) ";") (x::xs)
        else if hd==andc then
         Format.fprintf f "(%a)" (pplist (aux depth) ",") (x::xs)
        else if hd==rimplc then (
          assert (List.length xs = 1);
          Format.fprintf f "@[<hov 1>(%a@ :-@ %a)@]" (aux depth) x (aux depth) (List.hd xs)
        ) else if hd==implc then (
          assert (List.length xs = 1);
          Format.fprintf f "@[<hov 1>(%a@ =>@ %a)@]" (aux depth) x (aux depth) (List.hd xs)
        ) else pp_app f ppconstant (aux depth) (hd,x::xs)
    | Custom (hd,xs) -> pp_app f ppconstant (aux depth) (hd,xs)
    | UVar (r,vardepth,argsno) when not nice ->
       let args = mkinterval vardepth argsno 0 in
       pp_app f (pp_uvar depth vardepth 0) ppconstant (r,args)
    | UVar (r,vardepth,argsno) when !r == dummy ->
       let diff = vardepth - depth0 in
       let diff = if diff >= 0 then diff else 0 in
       let vardepth = vardepth - diff in
       let argsno = argsno + diff in
       let args = mkinterval vardepth argsno 0 in
       pp_app f (pp_uvar depth vardepth 0) ppconstant (r,args)
    | UVar (r,vardepth,argsno) ->
       pp_uvar depth vardepth argsno f r
    | AppUVar (r,vardepth,terms) when !r != dummy && nice -> 
       aux depth f (!do_app_deref ~from:vardepth ~to_:depth terms !r)
    | AppUVar (r,vardepth,terms) -> 
       pp_app f (pp_uvar depth vardepth 0) (aux depth) (r,terms)
    | Arg (n,argsno) ->
       let args = mkinterval argsdepth argsno 0 in
       pp_app f (pp_arg depth) ppconstant (n,args)
    | AppArg (v,terms) ->
       pp_app f (pp_arg depth) (aux depth) (v,terms) 
    | Const s -> ppconstant f s 
    | Lam t ->
       let c = constant_of_dbl depth in
       Format.fprintf f "%a\\%a%!" (aux depth) c (aux (depth+1)) t;
    | String str -> Format.fprintf f "\"%s\"" (Parser.ASTFuncS.pp str)
    | Int i -> Format.fprintf f "%d" i
    | Float x -> Format.fprintf f "%f" x
  in
    aux depth0 f t
;;

(* pp for first-order prolog *) 
let xppterm_prolog ~nice names env f t =
  let pp_app f pphd pparg (hd,args) =
   if args = [] then pphd f hd
   else begin
    Format.fprintf f "@[<hov 1>%a(%a@]" pphd hd (pplist pparg ",") args;
    Format.fprintf f "%s" ")";
   end in
  let ppconstant f c = Format.fprintf f "%s" (string_of_constant c) in
  let rec pp_arg f n =
   let name= try List.nth names n with Failure _ -> "A" ^ string_of_int n in
   if env.(n) == dummy then Format.fprintf f "%s" name
   (* TODO: (potential?) bug here, the argument is not lifted
      from g_depth (currently not even passed to the function)
      to depth (not passed as well) *)
   else if nice then aux f env.(n)
   else Format.fprintf f "≪%a≫ " aux env.(n)
  and aux f = function
      App (hd,x,xs) ->
        if hd==eqc then
         Format.fprintf f "@[<hov 1>%a@ =@ %a@]" aux x aux (List.hd xs) 
        else if hd==orc then        
                       (* (%a) ? *)
         Format.fprintf f "%a" (pplist aux ";") (x::xs)  
        else if hd==andc then    
         Format.fprintf f "%a" (pplist aux ",") (x::xs)  
        else if hd==rimplc then (
          assert (List.length xs = 1);
          Format.fprintf f "@[<hov 1>(%a@ :-@ %a@])" aux x aux (List.hd xs)
        ) else pp_app f ppconstant aux (hd,x::xs) 
    | Custom (hd,xs) ->  assert false;
    | UVar _
    | AppUVar _ -> assert false
    | Arg (n,0) -> pp_arg f n
    | Arg _
    | AppArg(_,_) -> assert false
    | Const s -> ppconstant f s
    | Lam t -> assert false;
    | String str -> Format.fprintf f "\"%s\"" (Parser.ASTFuncS.pp str)
    | Int i -> Format.fprintf f "%d" i
    | Float x -> Format.fprintf f "%f" x
  in
    aux f t
;;

let ppterm = xppterm ~nice:false
let uppterm = xppterm ~nice:true
let pp_FOprolog = xppterm_prolog ~nice:true 

end (* }}} *)
open Pp

type key1 = int
type key2 = int
type key = key1 * key2

type clause =
 { depth : int; args : term list; hyps : term list; vars : int; key : key }

let ppclause f { args = args; hyps = hyps; key = (hd,_) } =
  Format.fprintf f "@[<hov 1>%s %a :- %a.@]" (string_of_constant hd)
     (pplist (uppterm 0 [] 0 [||]) "") args
     (pplist (uppterm 0 [] 0 [||]) ",") hyps

(* {{{ ************** to_heap/restrict/deref ******************** *)

exception NotInTheFragment
(* in_fragment n [n;...;n+m-1] = m *)
let rec in_fragment expected =
 function
   [] -> 0
 | Const c::tl when c = expected -> 1 + in_fragment (expected+1) tl
 | _ -> raise NotInTheFragment

exception RestrictionFailure

(* To_heap performs at once:
   1) refreshing of the arguments into variables (heapifycation)
   2) restriction/occur-check (see restrict function below)

   when from = to, i.e. delta = 0:
     (-infty,+infty) -> (-infty,+infty)
   when from < to, i.e. delta < 0:
     (-infty,from) -> (-infty,from)   free variables
     [from,+infty) -> [to,+infty)     bound variables
   when from > to, i.e. delta > 0:
     (-infty,to)   -> (-infty,to)     free variables
     [to,from)     -> error           free restricted variables
     [from,+infty) -> [to,+infty)     bound variables
   
   Invariant:
     when from=to, to_heap is to be called only for terms that are not in the
     heap
*)

let def_avoid = ref dummy
let occurr_check r1 r2 = if r1 == r2 then raise RestrictionFailure

let dummy_trail = ref []
let dummy_env = [||]

let rec to_heap argsdepth last_call trail ~from ~to_ ?(avoid=def_avoid) e t =
  let delta = from - to_ in
  let rec aux depth x =
    TRACE "to_heap" (fun fmt -> Format.fprintf fmt "to_heap(%d,%d->%d): %a"
      depth from to_ (ppterm depth [] argsdepth e) x)
    match x with
    | Const c ->
       if delta == 0 then x else                          (* optimization  *)
       if c >= from then constant_of_dbl (c - delta) else (* locally bound *)
       if c < to_ then x else                             (* constant      *)
       raise RestrictionFailure
    | Lam f ->
       let f' = aux (depth+1) f in
       if f == f' then x else Lam f'
    | App (c,t,l) when delta == 0 || c < from && c < to_ ->
       let t' = aux depth t in
       let l' = smart_map (aux depth) l in
       if t == t' && l == l' then x else App (c,t',l')
    | App (c,t,l) when c >= from ->
       App(c-delta, aux depth t, smart_map (aux depth) l)
    | App _ -> raise RestrictionFailure
    | Custom (c,l) ->
       let l' = smart_map (aux depth) l in
       if l == l' then x else Custom (c,l')
    | String _
    | Int _
    | Float _ -> x

    (* fast path with no deref... *)
    | UVar (r,_,_) when delta == 0 -> occurr_check avoid r; x

    (* deref and Arg->UVar *)
    | UVar ({ contents = t },vardepth,args) when t != dummy ->
       if depth == 0 then
         full_deref argsdepth last_call trail ~from:vardepth ~to_ args e t
       else
         (* First phase: from vardepth to from+depth *)
         let t =
            full_deref argsdepth last_call trail
              ~from:vardepth ~to_:(from+depth) args e t in
         (* Second phase: from from to to *)
         aux depth t
    | AppUVar ({contents=t},vardepth,args) when t != dummy ->
       if depth == 0 then
         app_deref ~from:vardepth ~to_ args t
       else
         (* First phase: from vardepth to from+depth *)
         let t = app_deref ~from:vardepth ~to_:(from+depth) args t in
         (* Second phase: from from to to *)
         aux depth t
    | Arg (i,args) when argsdepth >= to_ ->
       let a = e.(i) in
       if a == dummy then
         let r = ref dummy in
         let v = UVar(r,to_,0) in
         e.(i) <- v;
         if args == 0 then v else UVar(r,to_,args)
       else
         full_deref argsdepth last_call trail
           ~from:argsdepth ~to_:(to_+depth) args e a
    | AppArg(i,args) when argsdepth >= to_ ->
       let a = e.(i) in
       if a == dummy then
         let r = ref dummy in
         let v = UVar(r,to_,0) in
         e.(i) <- v;
         AppUVar(r,to_,args) 
       else
         let args = List.map (aux depth) args in
         app_deref ~from:argsdepth ~to_:(to_+depth) args a

    (* pruning *)
    | UVar (r,vardepth,0) when delta > 0 ->
       occurr_check avoid r;
       if vardepth <= to_ then x
       else
         let fresh = UVar(ref dummy,to_,0) in
         if not last_call then trail := r :: !trail;
         r := fresh;
        (* TODO: test if it is more efficient here to return fresh or
           the original, imperatively changed, term. The current solution
           avoids dereference chains, but puts more pressure on the GC. *)
         fresh
    | UVar (r,vardepth,argsno) when delta < 0 ->
       occurr_check avoid r;
       if vardepth+argsno <= from then x
       else
        let r,vardepth,argsno =
          decrease_depth r ~from:vardepth ~to_:from argsno in
        let args = mkinterval vardepth argsno 0 in
        let args = List.map (fun c -> aux depth (constant_of_dbl c)) args in
        AppUVar (r,vardepth,args)
    | AppUVar (r,vardepth,args) when delta < 0 ->
       occurr_check avoid r;
       let r,vardepth,argsno =
         decrease_depth r ~from:vardepth ~to_:from 0 in
       let args0= List.map constant_of_dbl (mkinterval vardepth argsno 0) in
       let args = List.map (aux depth) (args0@args) in
       AppUVar (r,vardepth,args)

    | UVar _ -> error "Non trivial pruning not implemented"
    | AppUVar _ -> error "Non trivial pruning not implemented"
    | Arg _ -> anomaly "to_heap: Arg: argsdepth < to_"
    | AppArg _ -> anomaly "to_heap: AppArg: argsdepth < to_"
  in
    aux 0 t

(* full_deref performs lifting only and with from <= to
   if called on non-heap terms, it does not turn them to heap terms
   (if from=to_)

   Note:
     when full_deref is called inside restrict, it may be from > to_
     t lives in from; args already live in to_
*)
and full_deref argsdepth last_call trail ~from ~to_ args e t =
  TRACE "full_deref" (fun fmt ->
    Format.fprintf fmt "full_deref from:%d to:%d %a @@ %d\n%!"
      from to_ (ppterm from [] 0 e) t args)
 if args == 0 then
   if from == to_ then t
   else to_heap argsdepth last_call trail ~from ~to_ e t
 else (* O(1) reduction fragment tested here *)
   let from,args',t = eat_args from args t in
   let t = full_deref argsdepth last_call trail ~from ~to_ 0 e t in
   if args' == 0 then t
   else
     match t with
     | Lam _ -> anomaly "eat_args went crazy"
     | Const c ->
        let args = mkinterval (from+1) (args'-1) 0 in
        App (c,constant_of_dbl from,List.map constant_of_dbl args)
     | App (c,arg,args2) ->
        let args = mkinterval from args' 0 in
        App (c,arg,args2 @ List.map constant_of_dbl args)
     | Custom (c,args2) ->
        let args = mkinterval from args' 0 in
        Custom (c,args2@List.map constant_of_dbl args)
     (* TODO: when the UVar/Arg is not dummy, we call full_deref that
        will call to_heap that will call_full_deref again. Optimize the
        path *)
     | UVar(t,depth,args2) when from = depth+args2 ->
        UVar(t,depth,args2+args')
     | AppUVar (r,depth,args2) ->
        let args = mkinterval from args' 0 in
        AppUVar (r,depth,args2@List.map constant_of_dbl args)
     | Arg(i,args2) when from = argsdepth+args2 -> Arg(i,args2+args')
     | AppArg (i,args2) ->
        let args = mkinterval from args' 0 in
        AppArg (i,args2@List.map constant_of_dbl args)
     | Arg(i,argsno) ->
        let args1 = mkinterval argsdepth argsno 0 in
        let args2 = mkinterval from args' 0 in
        let args = List.map constant_of_dbl (args1@args2) in
        AppArg (i,args)
     | UVar (r,vardepth,argsno) ->
        let args1 = mkinterval vardepth argsno 0 in
        let args2 = mkinterval from args' 0 in
        let args = List.map constant_of_dbl (args1@args2) in
        AppUVar (r,vardepth,args)
     | String _
     | Int _
     | Float _ -> t

(* eat_args n [n ; ... ; n+k] (Lam_0 ... (Lam_k t)...) = n+k+1,[],t
   eat_args n [n ; ... ; n+k]@l (Lam_0 ... (Lam_k t)...) =
     n+k+1,l,t if t != Lam or List.hd l != n+k+1 *)
and eat_args depth l t =
  match t with
  | Lam t' when l > 0 -> eat_args (depth+1) (l-1) t'
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     eat_args depth l (deref ~from:origdepth ~to_:depth args t)
  | AppUVar  ({contents=t},origdepth,args) when t != dummy ->
     eat_args depth l (app_deref ~from:origdepth ~to_:depth args t)
  | _ -> depth,l,t

(* Lift is to be called only on heap terms and with from <= to *)
(* TODO: use lift in fullderef? efficient iff it is inlined *)
and lift ~from ~to_ t =
 (* Dummy trail, argsdepth and e: they won't be used *)
 if from == to_ then t
 else to_heap 0 false dummy_trail ~from ~to_ dummy_env t

(* Deref is to be called only on heap terms and with from <= to *)
and deref ~from ~to_ args t =
 (* Dummy trail, argsdepth and e: they won't be used *)
 full_deref 0 false dummy_trail ~from ~to_ args dummy_env t

(* UVar(_,from,argsno) -> Uvar(_,to_,argsno+from-to_) *)
and decrease_depth r ~from ~to_ argsno =
 if from <= to_ then r,from,argsno
 else
  let newr = ref dummy in
  let newargsno = argsno+from-to_ in
  let newvar = UVar(newr,to_,newargsno) in
  (* TODO: here we are not registering the operation in the
     trail to avoid passing last_call/trail around in every single
     function. Decrease_depth is reversible. However, does this slow
     down? Would using a global last_call/trail speed up things? What
     about passing around last_call/trail?
  if not last_call then trail := r :: !trail;*)
  r := newvar;
  newr,to_,newargsno

(* simultaneous substitution of ts for [depth,depth+|ts|)
   the substituted term must be in the heap
   the term is delifted by |ts|
   every t in ts must be either an heap term or an Arg(i,0)
   the ts are lifted as usual *)
and subst fromdepth ts t =
 TRACE "subst" (fun fmt ->
   Format.fprintf fmt "@[<hov 2>subst@ t: %a@ ts: %a@]"
   (uppterm 0 [] 0 [||]) t (pplist (uppterm 0 [] 0 [||]) ",") ts)
 if ts == [] then t
 else
   let len = List.length ts in
   let fromdepthlen = fromdepth + len in
   let rec aux depth = function
   | Const c as x ->
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (c-fromdepth) with
        | Arg(i,0) as t -> t 
        | t -> lift ~from:fromdepth ~to_:(depth-len) t
      else if c < fromdepth then x
      else constant_of_dbl (c-len) (* NOT LIFTED *)
   | Arg _ | AppArg _ -> anomaly "subst takes a heap term"
   | App(c,x,xs) as orig ->
      let x' = aux depth x in
      let xs' = List.map (aux depth) xs in
      let xxs' = x'::xs' in
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (c-fromdepth) with
        | Arg(i,0) -> begin
           try Arg(i,in_fragment fromdepth xxs')
           with NotInTheFragment -> AppArg (i,xxs') end
        | t ->
           let t = lift ~from:fromdepth ~to_:depth t in
           beta depth [] t xxs'
      else if c < fromdepth then
        if x==x' && xs==xs' then orig else App(c,x',xs')
      else App(c-len,x',xs')
   | Custom(c,xs) as orig ->
      let xs' = List.map (aux depth) xs in
      if xs==xs' then orig else Custom(c,xs')
   | UVar({contents=g},vardepth,argsno) when g != dummy ->
      aux depth (deref ~from:vardepth ~to_:depth argsno g)
   | UVar(r,vardepth,argsno) as orig ->
      if vardepth+argsno <= fromdepth then orig
      else
       let r,vardepth,argsno =
         decrease_depth r ~from:vardepth ~to_:fromdepth argsno in
       let args = mkinterval vardepth argsno 0 in
       let args = List.map (fun c -> aux depth (constant_of_dbl c)) args in
       (* XXX TODO: check if we can stay in the fragment, here and in
          many other places *)
       AppUVar (r,vardepth,args)
   | AppUVar({ contents = t },vardepth,args) when t != dummy ->
      aux depth (app_deref ~from:vardepth ~to_:depth args t)
   | AppUVar(r,vardepth,args) ->
      let r,vardepth,argsno =
        decrease_depth r ~from:vardepth ~to_:fromdepth 0 in
      let args0 = List.map constant_of_dbl (mkinterval vardepth argsno 0) in
      let args = List.map (aux depth) (args0@args) in
      AppUVar(r,vardepth,args)
   | Lam t -> Lam (aux (depth+1) t)
   | String _
   | Int _
   | Float _ as x -> x
   in
     aux fromdepthlen t

and beta depth sub t args =
 match t,args with
 | Lam t',hd::tl -> beta depth (hd::sub) t' tl
 | _ ->
    let t' = subst depth sub t in
    match args with
    | [] -> t'
    | ahd::atl ->
         match t' with
         | Const c -> App (c,ahd,atl)
         | Arg _
         | AppArg _ -> anomaly "beta takes only heap terms"
         | App (c,arg,args1) -> App (c,arg,args1@args)
         | Custom (c,args1) -> Custom (c,args1@args)
         | UVar (r,n,m) -> begin
            try UVar(r,n,m + in_fragment (n+m) args)
            with NotInTheFragment ->
              let args1 = List.map constant_of_dbl (mkinterval n m 0) in
              AppUVar (r,n,args1@args) end
         | AppUVar (r,depth,args1) -> AppUVar (r,depth,args1@args)
         | Lam _ -> anomaly "beta: some args and some lambdas"
         | String _ | Int _ | Float _ -> type_error "beta"

(* Deref is to be called only on heap terms and with from <= to *)
and app_deref ~from ~to_ args t = beta to_ [] (deref ~from ~to_ 0 t) args
;;

let () = Pp.do_deref := deref;;
let () = Pp.do_app_deref := app_deref;;

(* Restrict is to be called only on heap terms *)
let restrict ?avoid argsdepth last_call trail ~from ~to_ e t =
 if from = to_ && avoid == None then t
 else to_heap ?avoid argsdepth last_call trail ~from ~to_ e t

(* }}} *)
(* {{{ ************** indexing ********************************** *)

module Indexing : sig

  type index
  val key_of : constant -> term -> key
  val add_clauses : clause list -> index -> index
  val get_clauses : constant -> term -> index -> clause list
  val make : clause list -> index

end = struct (* {{{ *)

(* all clauses: used when the query is flexible
   all flexible clauses: used when the query is rigid and the map
                        for that atom is empty
   map: used when the query is rigid before trying the all flexible clauses *)
type index = (clause list * clause list * clause list Ptmap.t) Ptmap.t

let variablek =    -99999999
let abstractionk = -99999998

let key_of depth =
 let rec skey_of = function
    Const k -> k
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (deref ~from:origdepth ~to_:depth args t)
  | AppUVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (app_deref ~from:origdepth ~to_:depth args t)
  | App (k,_,_)
  | Custom (k,_) -> k
  | Lam _ -> abstractionk
  | Arg _ | UVar _ | AppArg _ | AppUVar _ -> variablek
  | String str -> 
     let hash = -(Hashtbl.hash str) in
     if hash > abstractionk then hash
     else hash+2 
  | Int i -> 
     let hash = -(Hashtbl.hash i) in
     if hash > abstractionk then hash
     else hash+1024
  | Float f -> 
     let hash = -(Hashtbl.hash f) in
     if hash > abstractionk then hash
     else hash+1024 in           
 let rec key_of_depth = function
   Const k -> k, variablek
 | UVar ({contents=t},origdepth,args) when t != dummy ->
    (* TODO: optimization: avoid dereferencing *)
    key_of_depth (deref ~from:origdepth ~to_:depth args t)
 | AppUVar ({contents=t},origdepth,args) when t != dummy -> 
    key_of_depth (app_deref ~from:origdepth ~to_:depth args t)
 | App (k,arg2,_) -> k, skey_of arg2
 | Custom _ -> assert false
 | Arg _ | AppArg _ | Lam _ | UVar _ | AppUVar _ | String _ | Int _ | Float _->
    raise (Failure "Not a predicate")
 in
  key_of_depth

module IndexData =
 struct
  (* Note: we tried (c79d0e3007f66eb553b6d50338faca1e09d8d064) replacing
     string with string*int in Const to index only the (unique) integer and
     speed up comparison w.r.t. String.compare. But it seems that always
     projecting out the integer from the pair during indexing for clause
     retrieval makes the example program slower. *)
  type t = key1
  let equal = (==)
  let compare (x:int) (y:int) = y - x
end

let get_clauses depth a m =
 let ind,app = key_of depth a in
 try
  let l,flexs,h = Ptmap.find ind m in
  if app=variablek then l
  else (try Ptmap.find app h with Not_found -> flexs)
 with Not_found -> []

let add_clauses clauses p =       
  List.fold_left (fun m clause -> 
    let ind,app = clause.key in
    try 
      let l,flexs,h = Ptmap.find ind m in
      if app=variablek then
       Ptmap.add ind
        (clause::l,clause::flexs,Ptmap.map(fun l_rev->clause::l_rev) h)
        m
      else
       let l_rev = try Ptmap.find app h with Not_found -> flexs in
        Ptmap.add ind
         (clause::l,flexs,Ptmap.add app (clause::l_rev) h) m
    with Not_found -> 
     if app=variablek then
      Ptmap.add ind ([clause],[clause],Ptmap.empty) m
     else
      Ptmap.add ind
       ([clause],[],Ptmap.add app [clause] Ptmap.empty) m
    ) p clauses

let make p = add_clauses (List.rev p) Ptmap.empty

end (* }}} *)
open Indexing


(* }}} *)
(* {{{ ************** unification ******************************* *)

let rec make_lambdas destdepth args =
 if args = 0 then UVar(ref dummy,destdepth,0)
 else Lam (make_lambdas (destdepth+1) (args-1))

(* Invariants:                                          |
   adepth: depth of a (query, heap term)                - bdepth       b
   bdepth: depth of b (clause hd, stack term in env e)  | b-only       .
   adepth >= bdepth                                     - adepth  a =  .
                                                        | local   x\   x\
                                                        -          a' = b'
   Spec:
   (-infy,bdepth) = (-infty,bdepth)   common free variables
   [bdepth,adepth)                    free variable only visible by one:fail
   [adepth,+infty) = [bdepth,+infy)   bound variables

   Names:
   delta = adepth - bdepth i.e. size of forbidden region
   heap = ???

   Note about dereferencing UVar(r,origdepth,args):
   - args live *here* (a/bdepth + depth)
   - !r lives in origdepth
   + we deref to move everything to a/bdepth + depth
   
   Note about dereferencing Arg(i,args):
   - args live *here* (bdepth + depth)
   - e.(i) lives in bdepth
   + we deref to move everything to adepth + depth
*)
let unif trail last_call adepth e bdepth a b =

 (* heap=true if b is known to be a heap term *)
 let rec unif depth a bdepth b heap =
   TRACE "unif" (fun fmt ->
     Format.fprintf fmt "unif: @[<hov 2>^%d:%a@ =%d= ^%d:%a@]"
       adepth (ppterm depth [] adepth [||]) a depth
       bdepth (ppterm depth [] adepth e) b)
   let unif d a bd b h = TCALL unif d a bd b h in
   let delta = adepth - bdepth in
   (delta = 0 && a == b) || match a,b with
(* TODO: test if it is better to deref first or not, i.e. the relative order
   of the clauses below *)
   | UVar(r1,_,args1), UVar(r2,_,args2) when r1 == r2 -> args1 == args2

   (* deref *)
   | UVar ({ contents = t }, from, args), _ when t != dummy ->
      unif depth (deref ~from ~to_:(adepth+depth) args t) bdepth b heap
   | AppUVar ({ contents = t }, from, args), _ when t != dummy -> 
      unif depth (app_deref ~from ~to_:(adepth+depth) args t) bdepth b heap
   | _, UVar ({ contents = t }, from, args) when t != dummy ->
      unif depth a bdepth (deref ~from ~to_:(bdepth+depth) args t) true
   | _, AppUVar ({ contents = t }, from, args) when t != dummy ->
      unif depth a bdepth (app_deref ~from ~to_:(bdepth+depth) args t) true
   | _, Arg (i,args) when e.(i) != dummy ->
      (* XXX BROKEN deref invariant XXX
       *   args not living in to_ but in bdepth+depth *)
      unif depth a adepth
        (deref ~from:adepth ~to_:(adepth+depth) args e.(i)) true
   | _, AppArg (i,args) when e.(i) != dummy -> 
      (* XXX BROKEN deref invariant XXX
       *   args not living in to_ but in bdepth+depth *)
      unif depth a adepth
        (app_deref ~from:adepth ~to_:(adepth+depth) args e.(i)) true

   (* assign *)
   | _, Arg (i,0) ->
      e.(i) <-
       restrict adepth last_call trail ~from:(adepth+depth) ~to_:adepth e a;
      SPY "assign" (ppterm depth [] adepth [||]) (e.(i)); true
   | _, UVar (r,origdepth,0) ->
       if not last_call then trail := r :: !trail;
       begin try
         let t =
           if depth = 0 then
             restrict ~avoid:r adepth last_call trail
               ~from:adepth ~to_:origdepth e a
           else
             (* First step: we restrict the l.h.s. to the r.h.s. level *)
             let a =
               to_heap ~avoid:r adepth last_call trail
                 ~from:adepth ~to_:bdepth e a in
             (* Second step: we restrict the l.h.s. *)
             to_heap adepth last_call trail
               ~from:(bdepth+depth) ~to_:origdepth e a in
         r := t;
         SPY "assign" (ppterm depth [] adepth [||]) t; true
       with RestrictionFailure -> false end
   | UVar (r,origdepth,0), _ ->
       if not last_call then trail := r :: !trail;
       begin try
         let t =
           if depth=0 then
             if origdepth = bdepth && heap then b
             else
               to_heap ~avoid:r adepth last_call trail
                 ~from:bdepth ~to_:origdepth e b
           else
             (* First step: we lift the r.h.s. to the l.h.s. level *)
             let b =
               to_heap ~avoid:r adepth last_call trail
                 ~from:bdepth ~to_:adepth e b in
             (* Second step: we restrict the r.h.s. *)
             to_heap adepth last_call trail
               ~from:(adepth+depth) ~to_:origdepth e b in
         r := t;
         SPY "assign" (ppterm depth [] adepth [||]) t; true
       with RestrictionFailure -> false end

   (* simplify *)
   (* TODO: unif->deref case. Rewrite the code to do the job directly? *)
   | _, Arg (i,args) ->
      e.(i) <- make_lambdas adepth args;
      SPY "assign" (ppterm depth [] adepth [||]) (e.(i));
      unif depth a bdepth b heap
   | _, UVar (r,origdepth,args) ->
      if not last_call then trail := r :: !trail;
      r := make_lambdas origdepth args;
      SPY "assign" (ppterm depth [] adepth [||]) (!r);
      unif depth a bdepth b heap
   | UVar (r,origdepth,args), _ ->
      if not last_call then trail := r :: !trail;
      r := make_lambdas origdepth args;
      SPY "assign" (ppterm depth [] adepth [||]) (!r);
      unif depth a bdepth b heap

   (* HO *)
   | AppUVar _, _
   | _, AppUVar _
   | AppArg _, _ -> error "HO unification (maybe delay)"

   (* recursion *)
   | App (c1,x2,xs), App (c2,y2,ys) ->
      (* Compressed cut&past from Const vs Const case below +
         delta=0 optimization for <c1,c2> and <x2,y2> *)
      ((delta=0 || c1 < bdepth) && c1=c2
       || c1 >= adepth && c1 = c2 + delta)
       &&
       (delta=0 && x2 == y2 || unif depth x2 bdepth y2 heap) &&
       for_all2 (fun x y -> unif depth x bdepth y heap) xs ys
   | Custom (c1,xs), Custom (c2,ys) ->
       (* Inefficient comparison *)
       c1 = c2 && for_all2 (fun x y -> unif depth x bdepth y heap) xs ys
   | Lam t1, Lam t2 -> unif (depth+1) t1 bdepth t2 heap
   | Const c1, Const c2 ->
      if c1 < bdepth then c1=c2 else c1 >= adepth && c1 = c2 + delta
   (*| Const c1, Const c2 when c1 < bdepth -> c1=c2
     | Const c, Const _ when c >= bdepth && c < adepth -> false
     | Const c1, Const c2 when c1 = c2 + delta -> true*)
   | Int s1, Int s2 -> s1==s2
   | Float s1, Float s2 -> s1==s2
   | String s1, String s2 -> s1==s2
   | _ -> false in
 unif 0 a bdepth b false
;;

(* Look in Git for Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower. *)

(* }}} *)
(* {{{ ************** backtracking ****************************** *)

type trail = term ref list ref

let undo_trail old_trail (trail :trail) =
  while !trail != old_trail do
    match !trail with
    | r :: rest -> r := dummy; trail := rest
    | _ -> assert false
  done
;;

type program = Indexing.index

(* The activation frames points to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. For bad reasons, we call it lvl in the code. *)
type frame =
 | FNil
(* TODO: to save memory, introduce a list of triples *)
 | FCons of (*lvl:*)alternative * ((*depth:*)int * program * term) list * frame
and alternative = {
  lvl : alternative;
  program : program;
  depth : int;
  goal : term;
  goals : ((*depth:*)int * program * term) list;
  stack : frame;
  trail : term ref list;
  clauses : clause list;
  next : alternative
}
let emptyalts : alternative = Obj.magic 0

let rec split_conj = function
  | App(c, hd, args) when c == andc ->
      split_conj hd @ List.(flatten (map split_conj args))
  | f when f == truec -> []
  | _ as f -> [ f ]
;;

(* BUG: the following clause is rejected because (Z c d) is not
   in the fragment. However, once X and Y becomes arguments, (Z c d)
   enters the fragment. 
r :- (pi X\ pi Y\ q X Y :- pi c\ pi d\ q (Z c d) (X c d) (Y c)) => ... *)

(* Takes the source of an implication an produces the clauses to be added to
 * the program *)
let rec clausify vars depth hyps ts = function
  | App(c, g, gs) when c == andc ->
     clausify vars depth hyps ts g @
     List.(flatten (map (clausify vars depth hyps ts) gs))
  | App(c, g2, [g1]) when c == rimplc ->
     let g1 = subst depth ts g1 in
     clausify vars depth (split_conj g1::hyps) ts g2
  | App(c, _, _) when c == rimplc -> assert false
  | App(c, g1, [g2]) when c == implc ->
     let g1 = subst depth ts g1 in
     clausify vars depth (split_conj g1::hyps) ts g2
  | App(c, _, _) when c == implc -> assert false
  | App(c, Lam b, []) when c == pic ->
     clausify (vars+1) depth hyps (ts@[Arg(vars,0)]) b
  | Const _ as g ->
     let g = subst depth ts g in
     [ { depth = depth; args = []; hyps = List.(flatten (rev hyps));
         vars = vars ; key = key_of depth g } ]
  | App _ as g ->
     begin match subst depth ts g with
     | App(_,x,xs) as g ->
         [ { depth = depth ; args=x::xs; hyps = List.(flatten (rev hyps));
             vars = vars; key = key_of depth g} ]
     | _ -> anomaly "subst went crazy" end
  | UVar ({ contents=g },from,args) when g != dummy ->
     clausify vars depth hyps ts
       (deref ~from ~to_:(depth+List.length ts) args g)
  | AppUVar ({contents=g},from,args) when g != dummy -> 
     clausify vars depth hyps ts
       (app_deref ~from ~to_:(depth+List.length ts) args g)
  | Arg _ | AppArg _ -> assert false 
  | Lam _ | Custom _ | String _ | Int _ | Float _ -> assert false
  | UVar _ | AppUVar _ -> assert false
;;

(* }}} *)
(* {{{ ************** run *************************************** *)

exception No_clause

let register_custom, lookup_custom =
 let (customs :
     ('a, depth:int -> env:term array -> term list -> unit) Hashtbl.t)
   =
     Hashtbl.create 17 in
 (fun s ->
    if s = "" || s.[0] <> '$' then
      error "Custom predicate name must begin with $";
    Hashtbl.add customs (fst (funct_of_ast (F.from_string s)))),
 Hashtbl.find customs
;;

let _ =
  register_custom "$print" (fun ~depth ~env args ->
    Format.printf "@[<hov 1>" ;
    List.iter (Format.printf "%a@ " (uppterm depth [] 0 env)) args;
    Format.printf "@]\n%!") ;
  register_custom "$lt" (fun ~depth ~env:_ args ->
    let rec get_constant = function
      | Const c -> c
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (app_deref ~from:vardepth ~to_:depth args t)
      | _ -> error "$lt takes constants as arguments" in
    match args with
    | [t1; t2] ->
        let t1 = get_constant t1 in
        let t2 = get_constant t2 in
        let is_lt = if t1 < 0 && t2 < 0 then t2 < t1 else t1 < t2 in
        if not is_lt then raise No_clause
    | _ -> type_error "$lt takes 2 arguments")
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ('a -> 'b -> 'k) * ('k -> 'k) =
  let trail = ref [] in

  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     depth >= 0 is the number of variables in the context. *)
  let rec run depth p g gs (next : frame) alts lvl =
    TRACE "run" (fun fmt -> ppterm depth [] 0 [||] fmt g)
    let run d p g gs n a l = TCALL run d p g gs n a l in
    match g with
    | c when c == cutc -> TCALL cut p gs next alts lvl
    | App(c, g, gs') when c == andc ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    | App(c, g1, [g2]) when c == implc ->
       let clauses = clausify 0 depth [] [] g1 in
       run depth (add_clauses clauses p) g2 gs next alts lvl
(*  This stays commented out because it slows down rev18 in a visible way!   *)
(*  | App(c, _, _) when c == implc -> anomaly "Implication must have 2 args" *)
    | App(c, g1, [g2]) when c == isc ->
       let eq = App(eqc, g1, [g2]) in
       run depth p eq gs next alts lvl 
    | App(c, Lam f, []) when c == pic ->
       run (depth+1) p f gs next alts lvl
    | App(c, Lam f, []) when c == sigmac ->
       let v = UVar(ref dummy, depth, 0) in
       run depth p (subst depth [v] f) gs next alts lvl
    | UVar ({ contents = g }, from, args) when g != dummy ->
       run depth p (deref ~from ~to_:depth args g) gs next alts lvl
    | AppUVar ({contents = t}, from, args) when t != dummy ->
       run depth p (app_deref ~from ~to_:depth args t) gs next alts lvl 
    | Const _ | App _ -> (* Atom case *)
       let cp = get_clauses depth g p in
       TCALL backchain depth p g gs cp next alts lvl
    | Arg _ | AppArg _ -> anomaly "Not a heap term"
    | Lam _ | String _ | Int _ | Float _ -> type_error "Not a predicate"
    | UVar _ | AppUVar _ -> error "Flexible predicate"
    | Custom(c, gs') ->
       let f = try lookup_custom c with Not_found -> anomaly"no such custom" in
       let b = try f depth [||] gs'; true with No_clause -> false in
       if b then
         match gs with
         | [] -> TCALL pop_andl alts next
         | (depth,p,g) :: gs -> run depth p g gs next alts lvl
       else TCALL next_alt alts

  and backchain depth p g gs cp next alts lvl =
    let last_call = alts == emptyalts in
    let rec args_of = function
      | Const _ -> []
      | App(_,x,xs) -> x::xs
      | UVar ({ contents = g },origdepth,args) when g != dummy ->
         args_of (deref ~from:origdepth ~to_:depth args g) 
      | AppUVar({ contents = g },origdepth,args) when g != dummy ->
         args_of (app_deref ~from:origdepth ~to_:depth args g) 
      | _ -> anomaly "ill-formed goal" in
    let args_of_g = args_of g in
    let rec select l =
      TRACE "select" (fun fmt -> pplist ~max:1 ~boxed:true ppclause "|" fmt l)
      match l with
      | [] -> TCALL next_alt alts
      | c :: cs ->
        let old_trail = !trail in
        let last_call = last_call && cs = [] in
        let env = Array.make c.vars dummy in
        match
         for_all2 (unif trail last_call depth env c.depth) args_of_g c.args
        with
        | false -> undo_trail old_trail trail; TCALL select cs
        | true ->
           let oldalts = alts in
           let alts = if cs = [] then alts else
             { program=p; depth = depth; goal=g; goals=gs; stack=next;
               trail=old_trail; clauses=cs; lvl = lvl ; next=alts} in
           begin match c.hyps with
           | [] ->
              begin match gs with
              | [] -> TCALL pop_andl alts next
              | (depth,p,g)::gs -> TCALL run depth p g gs next alts lvl end
           | h::hs ->
              let next = if gs = [] then next else FCons (lvl,gs,next) in
              let h =
                to_heap depth last_call trail ~from:c.depth ~to_:depth env h in
              let hs =
                List.map (fun x->
                  depth,p,
                  to_heap depth last_call trail ~from:c.depth ~to_:depth env x)
                hs in
              TCALL run depth p h hs next alts oldalts end
    in
      select cp

  and cut p gs next alts lvl =
    (* cut the or list until the last frame not to be cut (called lvl) *)
    let rec prune alts = if alts == lvl then alts else prune alts.next in
    let alts = prune alts in
    if alts == emptyalts then trail := [];
    match gs with
    | [] -> TCALL pop_andl alts next
    | (depth, p, g) :: gs -> TCALL run depth p g gs next alts lvl

  and pop_andl alts = function
    | FNil -> alts
    | FCons (_,[],_) -> anomaly "empty stack frame"
    | FCons(lvl,(depth,p,g)::gs,next) -> run depth p g gs next alts lvl

  and next_alt alts =
   if alts == emptyalts then raise No_clause
   else
    let { program = p; clauses = clauses; goal = g; goals = gs; stack = next;
          trail = old_trail; depth = depth; lvl = lvl; next = alts} = alts in
    undo_trail old_trail trail;
    backchain depth p g gs clauses next alts lvl
  in

  (* Finally the runtime *)
   (fun p (_,q_env,q) ->
     let q = to_heap 0 true trail ~from:0 ~to_:0 q_env q in
     run 0 p q [] FNil emptyalts emptyalts),
   next_alt
;;

(* }}} *)
(* {{{ ************** "compilation" + API *********************** *)

module AST = Parser
module ConstMap = Map.Make(Parser.ASTFuncS)

(* To assign Arg (i.e. stack) slots to unif variables in clauses *)
type argmap = { max_arg : int; name2arg : (string * term) list }

let empty_amap = { max_arg = 0; name2arg = [] }

let stack_var_of_ast ({ max_arg = f; name2arg = l } as amap) n =
 try amap, List.assoc n l
 with Not_found ->
  let n' = Arg (f,0) in
  { max_arg = f+1 ; name2arg = (n,n')::l }, n'
;;

let stack_funct_of_ast amap cmap f =
  try amap, ConstMap.find f cmap
  with Not_found ->
   let c = (F.pp f).[0] in
   if ('A' <= c && c <= 'Z') || c = '_' then
     let amap, v = stack_var_of_ast amap (F.pp f) in amap, v
   else amap, snd (funct_of_ast f)
;;

let rec stack_term_of_ast lvl amap cmap = function
  | AST.App(AST.Const f,[]) when F.eq f F.andf -> amap, truec
  | AST.Const f -> stack_funct_of_ast amap cmap f
  | AST.Custom f ->
     let cname = fst (funct_of_ast f) in
     begin try let _f = lookup_custom cname in ()
     with Not_found -> error ("No custom named " ^ F.pp f) end;
     amap, Custom (cname, [])
  | AST.App(AST.Const f, tl) ->
     let amap, rev_tl =
       List.fold_left (fun (amap, tl) t ->
         let amap, t = stack_term_of_ast lvl amap cmap t in
         (amap, t::tl))
        (amap, []) tl in
     let tl = List.rev rev_tl in
     let amap, c = stack_funct_of_ast amap cmap f in
     begin match c with
     | Arg (v,0) -> begin try
        let tl = in_fragment 0 tl in amap, Arg(v,tl)
        with NotInTheFragment -> amap, AppArg(v,tl) end
     | Const c -> begin match tl with
        | hd2::tl -> amap, App(c,hd2,tl)
        | _ -> anomaly "Application node with no arguments" end
     | _ -> error "Clause shape unsupported" end
  | AST.App (AST.Custom f,tl) ->
     let cname = fst (funct_of_ast f) in
     begin try let _f = lookup_custom cname in ()
     with Not_found -> error ("No custom named " ^ F.pp f) end;
     let amap, rev_tl =
       List.fold_left (fun (amap, tl) t ->
          let amap, t = stack_term_of_ast lvl amap cmap t in
          (amap, t::tl))
        (amap, []) tl in
     amap, Custom(cname, List.rev rev_tl)
  | AST.Lam (x,t) ->
     let cmap' = ConstMap.add x (constant_of_dbl lvl) cmap in
     let amap, t' = stack_term_of_ast (lvl+1) amap cmap' t in
     amap, Lam t'
  | AST.App (AST.App (f,l1),l2) ->
     stack_term_of_ast lvl amap cmap (AST.App (f, l1@l2))
  | AST.String str -> amap, String str
  | AST.Int i -> amap, Int i 
  | AST.Float f -> amap, Float f 
  | AST.App (AST.Lam _,_) -> error "Beta-redexes not in our language"
  | AST.App (AST.String _,_) -> error "Applied string value"
  | AST.App (AST.Int _,_) -> error "Applied integer value"
  | AST.App (AST.Float _,_) -> error "Applied float value"
;;
 
let query_of_ast t =
  let { max_arg = max; name2arg = l }, t =
    stack_term_of_ast 0 empty_amap ConstMap.empty t in
  List.rev_map fst l, Array.make max dummy, t
;;

let program_of_ast (p : Parser.clause list) : program =
 let clauses =
  List.concat
   (List.map (fun t ->
     let names,env,t = query_of_ast t in
     (* Format.eprintf "%a\n%!" (uppterm 0 names 0 env) t ; *)
     clausify (Array.length env) 0 [] [] t
   ) p) in
 Indexing.make clauses
;;

let pp_FOprolog p = assert false (*CSC: port the code, see function above List.iter (fun { Parser.head = a; hyps = f } ->
  let amap, cmap = empty_amap, ConstMap.empty in
  let amap, a = stack_term_of_ast 0 amap cmap a in
  let amap, f = stack_term_of_ast 0 amap cmap f in
  let { max_arg = max; name2arg = l } = amap in
  let names = List.rev_map fst l in
  let env = Array.make max dummy in
  if f = truec then
   Format.eprintf "@[<hov 1>%a%a.@]\n%!"
     (pp_FOprolog names env) a
     (pplist (pp_FOprolog names env) ",") (split_conj f)
  else
   Format.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
     (pp_FOprolog names env) a
     (pplist (pp_FOprolog names env) ",") (split_conj f)) p*)
;;

(* RUN with non indexed engine *)
type query = string list * term array * term
let pp_prolog = pp_FOprolog

let execute_once p q =
 let run, cont = make_runtime in
 try ignore (run p q) ; false
 with No_clause -> true
;;

let execute_loop p ((q_names,q_env,q) as qq) =
 let run, cont = make_runtime in
 let time0 = Unix.gettimeofday() in
 let k = ref (run p qq) in
 let time1 = Unix.gettimeofday() in
 prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
 Format.eprintf "Raw Result: %a\n%!" (ppterm 0 q_names 0 q_env) q ;
 Format.eprintf "Result: \n%!" ;
 List.iteri (fun i name -> Format.eprintf "%s=%a\n%!" name
  (uppterm 0 q_names 0 q_env) q_env.(i)) q_names;
 while !k != emptyalts do
   prerr_endline "More? (Y/n)";
   if read_line() = "n" then k := emptyalts else
    try
     let time0 = Unix.gettimeofday() in
     k := cont !k;
     let time1 = Unix.gettimeofday() in
     prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
     Format.eprintf "Raw Result: %a\n%!" (ppterm 0 q_names 0 q_env) q ;
     Format.eprintf "Result: \n%!" ;
     List.iteri (fun i name -> Format.eprintf "%s=%a\n%!" name
      (uppterm 0 q_names 0 q_env) q_env.(i)) q_names;
    with
     No_clause -> prerr_endline "Fail"; k := emptyalts
 done
;;

(* }}} *)

(* vim: set foldmethod=marker: *)
