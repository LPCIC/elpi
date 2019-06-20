(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module Fmt = Format
module F = Ast.Func
open Util
open Data
module C = Constants

(* Dereferencing an UVar(r,args) when !!r != dummy requires a function
   of this kind.  The pretty printer needs one but will only be defined
   later, since we need, for example, beta reduction to implement it *)
type 'args deref_fun =
  ?avoid:uvar_body -> from:int -> to_:int -> 'args -> term -> term

module Pp : sig
 
  (* Low level printing *)
  val ppterm : ?min_prec:int ->
    (*depth:*)int -> (*names:*)string list -> (*argsdepth:*)int -> env ->
    Fmt.formatter -> term -> unit

  (* For user consumption *)
  val uppterm : ?min_prec:int ->
    (*depth:*)int -> (*names:*)string list -> (*argsdepth:*)int -> env ->
    Fmt.formatter -> term -> unit

  (* To be assigned later, used to dereference an UVar/AppUVar *)
  val do_deref : int deref_fun ref
  val do_app_deref : term list deref_fun ref

end = struct (* {{{ *)

let do_deref = ref (fun ?avoid ~from ~to_ _ _ -> assert false);;
let do_app_deref = ref (fun ?avoid ~from ~to_ _ _ -> assert false);;
let m = ref [];;
let n = ref 0;;

let min_prec = Parser.min_precedence
let appl_prec = Parser.appl_precedence
let lam_prec = Parser.lam_precedence
let inf_prec = Parser.inf_precedence

let xppterm ~nice ?(min_prec=min_prec) depth0 names argsdepth env f t =
  let pp_app f pphd pparg ?pplastarg (hd,args) =
   if args = [] then pphd f hd
   else
    Fmt.fprintf f "@[<hov 1>%a@ %a@]" pphd hd
     (pplist pparg ?pplastelem:pplastarg " ") args in
  let ppconstant f c = Fmt.fprintf f "%s" (C.show c) in
  let rec pp_uvar prec depth vardepth args f r =
   if !!r == C.dummy then begin
    let s =
     try List.assq r !m
     with Not_found ->
      let s = "X" ^ string_of_int !n in
      incr n;
      m := (r,s)::!m;
      s
    in
     Fmt.fprintf f "%s%s%s" s
      (if vardepth=0 then "" else "^" ^ string_of_int vardepth)
      (if args=0 then "" else "+" ^ string_of_int args)
   end else if nice then begin
    aux prec depth f (!do_deref ~from:vardepth ~to_:depth args !!r)
   end else Fmt.fprintf f "<%a>_%d" (aux min_prec vardepth) !!r vardepth
  and pp_arg prec depth f n =
   let name= try List.nth names n with Failure _ -> "A" ^ string_of_int n in
   if try env.(n) == C.dummy with Invalid_argument _ -> true then
    Fmt.fprintf f "%s" name
   else if nice then begin
    if argsdepth <= depth then
     let dereffed = !do_deref ~from:argsdepth ~to_:depth 0 env.(n) in
     aux prec depth f dereffed
    else
     (* The instantiated Args live at an higher depth, and that's ok.
        But if we try to deref we make an imperative mess *)
     Fmt.fprintf f "≪%a≫_%d" (aux min_prec argsdepth) env.(n) argsdepth
   end else Fmt.fprintf f "≪%a≫_%d" (aux min_prec argsdepth) env.(n) argsdepth

  (* ::(a, ::(b, nil))  -->  [a,b] *)
  and flat_cons_to_list depth acc t = match t with
      UVar (r,vardepth,terms) when !!r != C.dummy -> 
       flat_cons_to_list depth acc
        (!do_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) when !!r != C.dummy -> 
       flat_cons_to_list depth acc
        (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | Cons (x,y) -> flat_cons_to_list depth (x::acc) y
    | _ -> List.rev acc, t
  and is_lambda depth =
   function
      Lam _ -> true
    | UVar (r,vardepth,terms) when !!r != C.dummy ->
       is_lambda depth (!do_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) when !!r != C.dummy -> 
       is_lambda depth (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | _ -> false
  and aux_last prec depth f t =
   if nice then begin
   match t with
     Lam _ -> aux min_prec depth f t
   | UVar (r,vardepth,terms) when !!r != C.dummy -> 
      aux_last prec depth f (!do_deref ~from:vardepth ~to_:depth terms !!r)
   | AppUVar (r,vardepth,terms) when !!r != C.dummy -> 
      aux_last prec depth f
       (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
   | _ -> aux prec depth f t
   end else aux inf_prec depth f t
  and aux prec depth f t =
   let with_parens ?(test=true) myprec h =
    if test && myprec < prec then
     (Fmt.fprintf f "(" ; h () ; Fmt.fprintf f ")")
    else h () in
   match t with
   | (Cons _ | Nil) ->
      let prefix,last = flat_cons_to_list depth [] t in
      Fmt.fprintf f "[" ;
      pplist ~boxed:true (aux Parser.list_element_prec depth) ", " f prefix ;
      if last != Nil then begin
       Fmt.fprintf f " | " ;
       aux prec 1 f last
      end;   
      Fmt.fprintf f "]"
    | Const s -> ppconstant f s 
    | App (hd,x,xs) ->
       (try
         let assoc,hdlvl =
          Parser.precedence_of (F.from_string (C.show hd)) in
         with_parens hdlvl
         (fun _ -> match assoc with
            Parser.Infix when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Parser.Infixl when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux hdlvl depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Parser.Infixr when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux hdlvl depth) (List.hd xs)
          | Parser.Prefix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" ppconstant hd
              (aux hdlvl depth) x
          | Parser.Postfix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" (aux hdlvl depth) x
              ppconstant hd 
          | _ ->
             pp_app f ppconstant (aux inf_prec depth)
              ~pplastarg:(aux_last inf_prec depth) (hd,x::xs))
        with Not_found -> 
         let lastarg = List.nth (x::xs) (List.length xs) in
         let hdlvl =
          if is_lambda depth lastarg then lam_prec
          else if hd == C.andc then 110 
          else appl_prec in
         with_parens hdlvl (fun _ ->
          if hd == C.andc then
            pplist (aux inf_prec depth) ~pplastelem:(aux_last inf_prec depth) ", " f (x::xs)
          else pp_app f ppconstant (aux inf_prec depth)
                 ~pplastarg:(aux_last inf_prec depth) (hd,x::xs)))
    | Builtin (hd,xs) ->
       with_parens appl_prec (fun _ ->
        pp_app f ppconstant (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (hd,xs))
    | UVar (r,vardepth,argsno) when not nice ->
       let args = List.map destConst (C.mkinterval vardepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        Fmt.fprintf f "." ;
        pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant (r,args))
    | UVar (r,vardepth,argsno) when !!r == C.dummy ->
       let diff = vardepth - depth0 in
       let diff = if diff >= 0 then diff else 0 in
       let vardepth = vardepth - diff in
       let argsno = argsno + diff in
       let args = List.map destConst (C.mkinterval vardepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant (r,args))
    | UVar (r,vardepth,argsno) ->
       pp_uvar prec depth vardepth argsno f r
    | AppUVar (r,vardepth,terms) when !!r != C.dummy && nice -> 
       aux prec depth f (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) -> 
       with_parens appl_prec (fun _ ->
        pp_app f (pp_uvar inf_prec depth vardepth 0) (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (r,terms))
    | Arg (n,argsno) ->
       let args = List.map destConst (C.mkinterval argsdepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        pp_app f (pp_arg prec depth) ppconstant (n,args))
    | AppArg (v,terms) ->
       with_parens appl_prec (fun _ ->
        pp_app f (pp_arg inf_prec depth) (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (v,terms))
    | Lam t ->
       with_parens lam_prec (fun _ ->
        let c = mkConst depth in
        Fmt.fprintf f "%a \\@ %a" (aux inf_prec depth) c
         (aux min_prec (depth+1)) t)
    | CData d -> CData.pp f d
    | Discard -> Fmt.fprintf f "_"
  in
    try aux min_prec depth0 f t with e -> Fmt.fprintf f "EXN PRINTING: %s" (Printexc.to_string e)
;;

let ppterm = xppterm ~nice:false
let uppterm = xppterm ~nice:true

let () = extend_printer pp_oref (fun fmt (id,t) ->
  if not (UUID.equal id id_term) then `Passed
  else
    let t : term = Obj.obj t in
    if t == C.dummy then Fmt.fprintf fmt "_"
    else uppterm 0  [] 0 empty_env fmt t;
    `Printed)

end (* }}} *)
open Pp

(******************************************************************************
  Stores for:
   - backtracking (trail)
   - constraints (delayed goals)
   - constraint handling rules (propagation rules)
  Note: propagation code for CHR rules is later
 ******************************************************************************)

let auxsg = ref []

let get_auxsg sg l =
   let rec aux i = function
      | []       -> assert false
      | hd :: tl ->
         if hd == sg then pred i else aux (pred i) tl
   in
   aux (List.length l) l

(* Together to hide low level APIs of ConstraintStore needed by Trail *)
module ConstraintStoreAndTrail : sig

  type propagation_item = {
     cstr : constraint_def;
     cstr_blockers : uvar_body list;
  }

  val new_delayed      : propagation_item list ref
  val to_resume        : stuck_goal list ref

  val declare_new : stuck_goal -> unit
  val remove_old : stuck_goal -> unit
  val remove_old_constraint : constraint_def -> unit

  val contents :
    ?overlapping:uvar_body list -> unit -> (constraint_def * blockers) list
  val print : Fmt.formatter -> (constraint_def * blockers) list -> unit
  val pp_stuck_goal : Fmt.formatter -> stuck_goal -> unit

  val state : state Fork.local_ref

  (* ---------------------------------------------------- *)

  type trail
 
  val empty : trail

  val initial_trail : trail Fork.local_ref
  val trail : trail Fork.local_ref
  val cut_trail : unit -> unit [@@inline]

  (* If true, no need to trail an imperative action.  Not part of trial_this
   * because you can save allocations and a function call by testing locally *)
  val last_call : bool ref

  (* add an item to the trail *)
  val trail_assignment : uvar_body -> unit           [@@inline]
  val trail_stuck_goal_addition : stuck_goal -> unit [@@inline]
  val trail_stuck_goal_removal : stuck_goal -> unit  [@@inline]

  (* backtrack *)
  val undo :
    old_trail:trail -> ?old_state:state -> unit -> unit

  val print_trail : Fmt.formatter -> unit

  (* ---------------------------------------------------- *)

  (* This is only used to know if the program execution is really over,
     I.e. to implement the last component of the runtime data type *)
  module Ugly : sig val delayed : stuck_goal list ref end

end = struct (* {{{ *)

 type propagation_item = {
    cstr : constraint_def;
    cstr_blockers : uvar_body list;
 }

  let state =
    Fork.new_local (State.init () |> State.end_compilation StrMap.empty)
  let read_custom_constraint ct =
    State.get ct !state
  let update_custom_constraint ct f =
    state := State.update ct !state f


type trail_item =
| Assignement of uvar_body
| StuckGoalAddition of stuck_goal
| StuckGoalRemoval of stuck_goal
[@@deriving show]

type trail = trail_item list
[@@deriving show]
let empty = []

let trail = Fork.new_local []
let initial_trail = Fork.new_local []
let last_call = Fork.new_local false;;

let cut_trail () = trail := !initial_trail [@@inlined];;

module Ugly = struct let delayed : stuck_goal list ref = Fork.new_local [] end
open Ugly
let contents ?overlapping () =
  let overlap : uvar_body list -> bool =
    match overlapping with
    | None -> fun _ -> true
    | Some l -> fun b -> List.exists (fun x -> List.memq x l) b in
  map_filter (function
    | { kind = Constraint c; blockers }
      when overlap blockers -> Some (c,blockers)
    | _ -> None) !delayed

let trail_assignment x = 
  [%spy "trail-this" (fun fmt i ->
     Fmt.fprintf fmt "last_call:%b item:%a" !last_call pp_trail_item (Assignement i)) x];
  if not !last_call then trail := Assignement x :: !trail
[@@inline]
;;
let trail_stuck_goal_addition x = 
  [%spy "trail-this" (fun fmt i ->
     Fmt.fprintf fmt "last_call:%b item:%a" !last_call pp_trail_item (StuckGoalAddition i)) x];
  if not !last_call then trail := StuckGoalAddition x :: !trail
[@@inline]
;;
let trail_stuck_goal_removal x = 
  [%spy "trail-this" (fun fmt i ->
     Fmt.fprintf fmt "last_call:%b item:%a" !last_call pp_trail_item (StuckGoalRemoval i)) x];
  if not !last_call then trail := StuckGoalRemoval x :: !trail
[@@inline]
;;

let remove ({ blockers } as sg) =
 [%spy "remove" (fun fmt -> Fmt.fprintf fmt "%a" pp_stuck_goal) sg];
 delayed := remove_from_list sg !delayed;
 List.iter (fun r -> r.rest <- remove_from_list sg r.rest) blockers

let add ({ blockers } as sg) =
 [%spy "add" (fun fmt -> Fmt.fprintf fmt "%a" pp_stuck_goal) sg];
 auxsg := sg :: !auxsg;
 delayed := sg :: !delayed;
 List.iter (fun r -> r.rest <- sg :: r.rest) blockers

let new_delayed = Fork.new_local []
let to_resume = Fork.new_local []

let print_trail fmt =
  pp_trail fmt !trail;
  Fmt.fprintf fmt "to_resume:%d new_delayed:%d\n%!"
    (List.length !to_resume) (List.length !new_delayed)

let declare_new sg =
  let blockers = uniqq sg.blockers in
  let sg = { sg with blockers } in
  add sg ;
  begin match sg.kind with
  | Unification _ -> ()
  | Constraint cstr ->
      new_delayed := { cstr; cstr_blockers = sg.blockers } :: !new_delayed
  end;
  (trail_stuck_goal_addition[@inlined]) sg

let remove_cstr_if_exists x l =
 let rec aux acc = function
   | [] -> l
   | { cstr = y } :: tl when x == y -> List.rev acc @ tl
   | y :: tl -> aux (y :: acc) tl
 in
  aux [] l

let remove_old cstr =
  remove cstr ;
  begin match cstr.kind with
  | Unification _ -> ()
  | Constraint c -> new_delayed := remove_cstr_if_exists c !new_delayed
  end;
  (trail_stuck_goal_removal[@inlined]) cstr
;;

let remove_old_constraint cd =
  let c = List.find
    (function { kind = Constraint x } -> x == cd | _ -> false) !delayed in
  remove_old c

let undo ~old_trail ?old_state () =
(* Invariant: to_resume and new_delayed are always empty when a choice
   point is created. This invariant is likely to break in the future,
   when we allow more interesting constraints and constraint propagation
   rules. *)
  to_resume := []; new_delayed := [];
  [%spy "trail-undo-from" pp_trail !trail];
  [%spy "trail-undo-to" pp_trail old_trail];
  while !trail != old_trail do
    match !trail with
    | Assignement r :: rest ->
       r.contents <- C.dummy;
       trail := rest
    | StuckGoalAddition sg :: rest -> remove sg; trail := rest
    | StuckGoalRemoval sg :: rest -> add sg; trail := rest
    | [] -> anomaly "undo to unknown trail"
  done;
  match old_state with
  | Some old_state -> state := old_state
  | None -> ()
;;

let print =
  let pp_depth fmt d =
    if d > 0 then
      Fmt.fprintf fmt "{%a} :@ "
        (pplist (uppterm d [] 0 empty_env) " ") (C.mkinterval 0 d 0) in
  let pp_ctx fmt ctx =
    if ctx <> [] then
     Fmt.fprintf fmt "@[<hov 2>%a@]@ ?- "
      (pplist (fun fmt { hdepth = d; hsrc = t } ->
                 uppterm d [] 0 empty_env fmt t) ", ") ctx in
  let pp_goal depth = uppterm depth [] 0 empty_env in
  pplist (fun fmt ({ cdepth=depth;context=pdiff; conclusion=g }, blockers) ->
    Fmt.fprintf fmt " @[<h>@[<hov 2>%a%a%a@]@  /* suspended on %a */@]"
      pp_depth depth
      pp_ctx pdiff
      (pp_goal depth) g
      (pplist (uppterm 0 [] 0 empty_env) ", ")
        (List.map (fun r -> UVar(r,0,0)) blockers)
  ) " "

let pp_stuck_goal fmt { kind; blockers } = match kind with
   | Unification { adepth = ad; env = e; bdepth = bd; a; b } ->
      Fmt.fprintf fmt
       " @[<h>@[<hov 2>^%d:%a@ == ^%d:%a@]@  /* suspended on %a */@]"
        ad (uppterm ad [] 0 empty_env) a
        bd (uppterm ad [] ad e) b
          (pplist ~boxed:false (uppterm 0 [] 0 empty_env) ", ")
            (List.map (fun r -> UVar(r,0,0)) blockers)
   | Constraint c -> print fmt [c,blockers]

end (* }}} *)
module T  = ConstraintStoreAndTrail
module CS = ConstraintStoreAndTrail

(* Assigning an UVar wakes up suspended goals/constraints *)
let (@:=) r v =
  (T.trail_assignment[@inlined]) r;
  if r.rest <> [] then
    begin
    [%spy "assign-to_resume" (fun fmt l ->
        Fmt.fprintf fmt "%d" (List.length l)) r.rest];
     CS.to_resume :=
      List.fold_right
       (fun x acc -> if List.memq x acc then acc else x::acc) r.rest
        !CS.to_resume
    end;
 r.contents <- v
;;
(******************************************************************************
  Unification (dereferencing and lift, to_heap)
 ******************************************************************************)

module HO : sig

  val unif : matching:bool -> int -> env -> int -> term -> term -> bool

  (* lift/restriction/heapification with occur_check *)
  val move : 
    adepth:int -> env -> ?avoid:uvar_body -> ?depth:int ->
    from:int -> to_:int -> term -> term
  
  (* like move but for heap terms (no heapification) *)
  val hmove :
    ?avoid:uvar_body ->
    from:int -> to_:int -> term -> term

  (* simultaneous substitution *)
  val subst : int -> term list -> term -> term

  val deref_uv : int deref_fun
  val deref_appuv : term list deref_fun

  val mkAppUVar : uvar_body -> int -> term list -> term
  val mkAppArg : int -> int -> term list -> term
  val is_flex : depth:int -> term -> uvar_body option
  val list_to_lp_list : term list -> term

  val mknLam : int -> term -> term

  val full_deref : adepth:int -> env -> depth:int -> term -> term

  (* Head of an heap term *)
  val deref_head : depth:int -> term -> term

  (* Put a flexible term in canonical expanded form: X^0 args.
   * It returns the canonical term and an assignment if needed.
   * (The first term is the result of dereferencing after the assignment) *)
  type assignment = uvar_body * int * term
  val expand_uv :
    depth:int -> uvar_body -> lvl:int -> ano:int -> term * assignment option
  val expand_appuv :
    depth:int -> uvar_body -> lvl:int -> args:term list -> term * assignment option

  val shift_bound_vars : depth:int -> to_:int -> term -> term

  val subtract_to_consts : amount:int -> depth:int -> term -> term

  val delay_hard_unif_problems : bool Fork.local_ref
    
end = struct 
(* {{{ *)

(* {{{ ************** move/hmove/deref_* ******************** *)

exception NotInTheFragment
(* in_fragment n [n;...;n+m-1] = m
   it must be called either on heap terms or on stack terms whose Args are
   non instantiated *)
let rec in_fragment expected =
 function
   [] -> 0
 | Const c::tl when c = expected -> 1 + in_fragment (expected+1) tl
 | UVar ({ contents = t} ,_,_)::tl -> (* XXX *)
    in_fragment expected (t :: tl)
(* Invariant not true anymore, since we may not deref aggressively
   to avoid occur-check
 | UVar (r,_,_)::_
 | AppUVar (r,_,_)::_ when !!r != C.dummy ->
     anomaly "non dereferenced terms in in_fragment"
*)
 | _ -> raise NotInTheFragment

exception NonMetaClosed

let deterministic_restriction e ~args_safe t =
 let rec aux =
  function
    Lam f -> aux f
  | App (_,t,l) -> aux t; List.iter aux l
  | Cons (x,xs) -> aux x; aux xs
  | Builtin (_,l) -> List.iter aux l
  | UVar (r,_,_) 
  | AppUVar (r,_,_) when !!r == C.dummy -> raise NonMetaClosed
  | UVar (r,_,_) -> aux !!r
  | AppUVar (r,_,l) -> aux !!r ; List.iter aux l
  | Arg (i,_) when e.(i) == C.dummy && not args_safe -> raise NonMetaClosed
  | AppArg (i,_) when e.(i) == C.dummy -> raise NonMetaClosed
  | Arg (i,_) -> if e.(i) != C.dummy then aux e.(i)
  | AppArg (i,l) -> aux e.(i) ; List.iter aux l
  | Const _
  | Nil
  | Discard
  | CData _ -> ()
 in
  try aux t ; true
  with NonMetaClosed -> false

exception RestrictionFailure

let occurr_check r1 r2 =
  match r1 with
  | None -> ()
  | Some r1 -> if r1 == r2 then raise RestrictionFailure

let rec make_lambdas destdepth args =
 if args = 0 then let x = UVar(oref C.dummy,destdepth,0) in x,x
 else let x,y = make_lambdas (destdepth+1) (args-1) in Lam x, y

let rec mknLam n x = if n = 0 then x else Lam (mknLam (n-1) x)

let mkAppUVar r lvl l =
  try UVar(r,lvl,in_fragment lvl l)
  with NotInTheFragment -> AppUVar(r,lvl,l)

let mkAppArg i fromdepth xxs' =
  try Arg(i,in_fragment fromdepth xxs')
  with NotInTheFragment -> AppArg (i,xxs')

(* move performs at once:
   1) refreshing of the arguments into variables (heapifycation)
   2) restriction/occur-check

   hmove is the variant that only does 2

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

   Notes:
    - remember that the depth of a stack term is the depth when the clause
      entered the program, whereas the argsdepth of the variables is the depth
      when the clause is used. Therefore it is normal to have arguments,
      possibly instantiated, whose depth is greater than the surrounding term.
      Calling to_heap on them with the wrong depth (e.g. the depth of the
      surrounding term) can therefore trigger restrictions that are meaningless.
    - it is possible for delta to be >0 (restriction) and the second term
      be a stack term. Therefore sometimes restrictions of heap terms are
      meaningful. Example:
      p A.
      |- pi x \ p X
      The unification problem becomes X^0 1^=^0 A^1 that triggers the
      assignment X^0 := to_heap ~from:1 ~to_:0 A^1
    - On the other hand *I think* that it is not possible to have
      argsdepth < to_ in to_heap.
      It would mean that I am doing an assignment
      X^to_ := ... A^argsdepth....
      that is triggered by an unification problem
      .... X^to_ .... == .... A^argsdepth ....
      that is triggered by calling a clause at depth argsdepth with a formal
      parameter containing an UVar whose depth is higher than the current depth
      of the program. How could such a variable enters the formal parameters
      without being restricted earlier?

      Therefore, in the case of heap terms, the invariant is
              from <= depthargs <= to_
      the first inequality because a clause always enter a program at a depth
      (from) smaller than when it is used (depthargs).
*)

(* [move ~from ~to ?avoid t] relocates a term t by amount (= to - from).
   In the diagrams below, c is a constant, l is locally bound variable
   (i.e. bound after from). The resulting term lives in the heap and avoid,
   if passed, is occur checked.

   - If amount is > 0 then Const nodes >= from are lifted by amount

       c1       --->   c1
       c2 from  --->   c2
       l3       -         to
       l4       -`->   l4
                 `->   l5

   - If amount is < 0 then Const nodes between to and from are ensured not
     to occur in the result, otherwise RestrictionFailure is raised.
     Const nodes >= from are de-lifted by amount

       c1       --->   c1 to                    c1       --->   c1 to
       c2 from  --->  Error                        from   ,->   l2   
       l3                                       l3       -,->   l3    
       l4                                       l4       -           

   * Property: move ~to ~from (move ~from ~to t) = t
     - if from <= to
     - if to > from and no Const >= to and < from occurs in t
       where occurs also means in the scope of an Uv

   * Args:
     - when defined in e the corresponding term lives in adepth
     - when undefined they are turned into Uv (heapification)
   
   * Uv occur check is performed only if avoid is passed
           
   * Deref under binders:
        from:2 to_:4
        G |- 3\ X^1 3         X := 2\f 1 2

        phase 1
        G |- 3\ (4\f 1 4) 3
        G |- 3\ f 1 3

        phase 2 (the lambda is anonymous, so 3\ is like 5\)
        G |- 5\ f 1 5
   
*)

let rec move ~adepth:argsdepth e ?avoid ?(depth=0) ~from ~to_ t =
(* TODO: to disable occur_check add something like: let avoid = None in *)
 let delta = from - to_ in
 let rc =
         if delta = 0 && e == empty_env && avoid == None then t (* Nothing to do! *)
 else begin
  (*if delta = 0 && e == empty_env && avoid <> None then prerr_endline "# EXPENSIVE OCCUR CHECK";*)
  let rec maux e depth x =
    [%trace "move" ("adepth:%d depth:%d from:%d to:%d x:%a"
        argsdepth depth from to_ (ppterm (from+depth) [] argsdepth e) x) begin
    match x with
    | Const c ->
       if delta == 0 then x else                          (* optimization  *)
       if c >= from then mkConst (c - delta) else (* locally bound *)
       if c < to_ then x else                             (* constant      *)
       raise RestrictionFailure
    | Lam f ->
       let f' = maux e (depth+1) f in
       if f == f' then x else Lam f'
    | App (c,t,l) when delta == 0 || c < from && c < to_ ->
       let t' = maux e depth t in
       let l' = smart_map (maux e depth) l in
       if t == t' && l == l' then x else App (c,t',l')
    | App (c,t,l) when c >= from ->
       App(c-delta, maux e depth t, smart_map (maux e depth) l)
    | App _ -> raise RestrictionFailure
    | Builtin (c,l) ->
       let l' = smart_map (maux e depth) l in
       if l == l' then x else Builtin (c,l')
    | CData _ -> x
    | Cons(hd,tl) ->
       let hd' = maux e depth hd in
       let tl' = maux e depth tl in
       if hd == hd' && tl == tl' then x else Cons(hd',tl')
    | Nil -> x
    | Discard -> x

    (* fast path with no deref... *)
    | UVar _ when delta == 0 && avoid == None -> x

    (* deref *)
    | UVar ({ contents = t }, vardepth, args) when t != C.dummy ->
       if depth == 0 then deref_uv ?avoid ~from:vardepth ~to_ args t
       else maux empty_env depth (deref_uv ~from:vardepth ~to_:(from+depth) args t)
    | AppUVar ({ contents = t }, vardepth, args) when t != C.dummy ->
       if depth == 0 then deref_appuv ?avoid ~from:vardepth ~to_ args t
       else maux empty_env depth (deref_appuv ~from:vardepth ~to_:(from+depth) args t)
    | Arg (i, args) when e.(i) != C.dummy ->
       deref_uv ?avoid ~from:argsdepth ~to_:(to_+depth) args e.(i)
    | AppArg(i, args) when e.(i) != C.dummy ->
       let args =
        try smart_map (maux e depth) args
        with RestrictionFailure ->
          anomaly "move: could check if unrestrictable args are unused" in
       deref_appuv ?avoid ~from:argsdepth ~to_:(to_+depth) args e.(i)

    (* heapification/restriction of Arg and AppArg *)
    | Arg (i, args) ->
       let to_ = min argsdepth to_ in
       let r = oref C.dummy in
       let v = UVar(r,to_,0) in
       e.(i) <- v;
       if args == 0 then v else UVar(r,to_,args)
    | AppArg(i, args) when
      List.for_all (deterministic_restriction e ~args_safe:(argsdepth=to_)) args
      ->
       let to_ = min argsdepth to_ in
       let args =
        try List.map (maux e depth) args
        with RestrictionFailure ->
         anomaly "TODO: implement deterministic restriction" in
       let r = oref C.dummy in
       let v = UVar(r,to_,0) in
       e.(i) <- v;
       mkAppUVar r to_ args
    | AppArg _ ->
       Fmt.fprintf Fmt.str_formatter
        "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
         (ppterm depth [] argsdepth e) x delta;
       anomaly (Fmt.flush_str_formatter ())

    (* restriction/lifting of UVar *)
    | UVar (r,vardepth,argsno) ->
       occurr_check avoid r;
       if delta <= 0 then (* to_ >= from *)
         if vardepth + argsno <= from then x
         else
           let r,vardepth,argsno =
             decrease_depth r ~from:vardepth ~to_:from argsno in
           let args = C.mkinterval vardepth argsno 0 in
           let args = List.map (maux empty_env depth) args in
           mkAppUVar r vardepth args
       else
         if vardepth + argsno <= to_ then x
         else
           let newt =
             let args = C.mkinterval vardepth (min argsno depth) 0 in
             let newvardepth = min to_ vardepth in
             let newvar = mkAppUVar (oref C.dummy) newvardepth args in
             mknLam argsno newvar
           in
           [%spy "assign (restriction)" (fun fmt _ -> Fmt.fprintf fmt "%d %a := %a" vardepth
              (uppterm (from+depth) [] argsdepth e) x
              (uppterm (vardepth) [] argsdepth e) newt) ()];
            r @:= newt;
            maux e depth (deref_uv ~from:vardepth ~to_:(from+depth) argsno newt)

    | AppUVar (r,vardepth,args) ->
       occurr_check avoid r;
       if delta < 0 then
         let r,vardepth,argsno =
           decrease_depth r ~from:vardepth ~to_:from 0 in
         let args0= C.mkinterval vardepth argsno 0 in
         let args =
          try List.map (maux e depth) (args0@args)
          with RestrictionFailure -> anomaly "impossible, delta < 0" in
         mkAppUVar r vardepth args
       else if delta == 0 then
         AppUVar (r,vardepth,List.map (maux e depth) args)
       else if List.for_all (deterministic_restriction e ~args_safe:(argsdepth=to_)) args then
         (* TODO: this branch is to be reviewed/tested throughly, unless
            Enrico is now confident with it *)
          let r,vardepth =
           if vardepth <= to_ then r,vardepth
           else begin
             let newvar = UVar(oref C.dummy,to_,0) in
             r @:= newvar;
             r,vardepth (*CSC: XXX why vardepth and not to_ ? *)
           end in
          (* Code for deterministic restriction *)
          let args =
           List.map (fun arg ->
            try Some (maux e depth arg) with RestrictionFailure -> None) args in
          let r,vardepth,args =
           if List.exists ((=) None) args then begin
            (* CSC: not optimized code, it does |args| intros even if one
               could sometimes save some abstractions *)
            let argslen = List.length args in
            let filteredargs = map_filter (fun x -> x) args in
            let r' = oref C.dummy in
            let newvar = mkAppUVar r' to_ filteredargs in
            r @:= mknLam argslen newvar;
            r',to_,filteredargs
           end else
            let args =
             List.map (function Some t -> t | None -> assert false) args in
            r,vardepth,args in
          mkAppUVar r vardepth args
       else begin
        Fmt.fprintf Fmt.str_formatter
         "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
          (ppterm depth [] argsdepth e) x delta;
        anomaly (Fmt.flush_str_formatter ())
       end
  end]
  in
   maux e depth t
  end
 in
  [%spy "move-output" (ppterm to_ [] argsdepth e) rc];
  rc

(* Hmove is like move for heap terms. By setting env to empty_env, it triggers
   fast paths in move (no need to heapify, the term already lives in the heap)*)
and hmove ?avoid ~from ~to_ t =
 [%trace "hmove" ("@[<hov 1>from:%d@ to:%d@ %a@]"
     from to_ (uppterm from [] 0 empty_env) t) begin
   move ?avoid ~adepth:0 ~from ~to_ empty_env t
 end]

(* UVar(_,from,argsno) -> Uvar(_,to_,argsno+from-to_) *)
and decrease_depth r ~from ~to_ argsno =
 if from <= to_ then r,from,argsno
 else
  let newr = oref C.dummy in
  let newargsno = argsno+from-to_ in
  let newvar = UVar(newr,to_,from-to_) in
  r @:= newvar;
  newr,to_,newargsno

(* simultaneous substitution of ts for [depth,depth+|ts|)
   the substituted term must be in the heap
   the term is delifted by |ts|
   every t in ts must be either an heap term or an Arg(i,0)
   the ts are lifted as usual *)
and subst fromdepth ts t =
 [%trace "subst" ("@[<hov 2>fromdepth:%d t: %a@ ts: %a@]" fromdepth
   (uppterm (fromdepth) [] 0 empty_env) t (pplist (uppterm fromdepth [] 0 empty_env) ", ") ts)
 begin
 if ts == [] then t
 else
   let len = List.length ts in
   let fromdepthlen = fromdepth + len in
   let rec aux depth tt =
   [%trace "subst-aux" ("@[<hov 2>t: %a@]" (uppterm (fromdepth+1) [] 0 empty_env) tt)
   begin match tt with
   | Const c as x ->
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
        | Arg(i,0) as t -> t 
        | t -> hmove ~from:fromdepth ~to_:(depth-len) t
      else if c < fromdepth then x
      else mkConst (c-len) (* NOT LIFTED *)
   | Arg _ | AppArg _ -> anomaly "subst takes a heap term"
   | App(c,x,xs) as orig ->
      let x' = aux depth x in
      let xs' = List.map (aux depth) xs in
      let xxs' = x'::xs' in
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
        | Arg(i,0) -> mkAppArg i fromdepth xxs'
        | t ->
           let t = hmove ~from:fromdepth ~to_:(depth-len) t in
           beta (depth-len) [] t xxs'
      else if c < fromdepth then
        if x==x' && xs==xs' then orig else App(c,x',xs')
      else App(c-len,x',xs')
   | Builtin(c,xs) as orig ->
      let xs' = List.map (aux depth) xs in
      if xs==xs' then orig else Builtin(c,xs')
   | Cons(hd,tl) as orig ->
       let hd' = aux depth hd in
       let tl' = aux depth tl in
       if hd == hd' && tl == tl' then orig else Cons(hd',tl')
   | Nil -> tt
   | Discard -> tt
   | UVar({contents=g},vardepth,argsno) when g != C.dummy ->
      [%tcall aux depth (deref_uv ~from:vardepth ~to_:depth argsno g)]
   | UVar(r,vardepth,argsno) as orig ->
      if vardepth+argsno <= fromdepth then orig
      else
       let r,vardepth,argsno =
         decrease_depth r ~from:vardepth ~to_:fromdepth argsno in
       let args = C.mkinterval vardepth argsno 0 in
       let args = List.map (aux depth) args in
       mkAppUVar r vardepth args
   | AppUVar({ contents = t },vardepth,args) when t != C.dummy ->
      [%tcall aux depth (deref_appuv ~from:vardepth ~to_:depth args t)]
   | AppUVar(r,vardepth,args) ->
      let r,vardepth,argsno =
        decrease_depth r ~from:vardepth ~to_:fromdepth 0 in
      let args0 = C.mkinterval vardepth argsno 0 in
      let args = List.map (aux depth) (args0@args) in
      mkAppUVar r vardepth args
   | Lam t -> Lam (aux (depth+1) t)
   | CData _ as x -> x
   end] in
     aux fromdepthlen t
 end]

and beta depth sub t args =
 [%trace "beta" ("@[<hov 2>subst@ t: %a@ args: %a@]"
     (uppterm (depth+List.length sub) [] 0 empty_env) t
     (pplist (uppterm depth [] 0 empty_env) ", ") args)
 begin match t, args with
 | UVar ({contents=g},vardepth,argsno), _ when g != C.dummy ->
    [%tcall beta depth sub
        (deref_uv ~from:vardepth ~to_:(depth+List.length sub) argsno g) args]
 | AppUVar({ contents=g },vardepth,uargs), _ when g != C.dummy ->
    [%tcall beta depth sub
         (deref_appuv ~from:vardepth ~to_:(depth+List.length sub) uargs g) args]
 | Lam t', hd::tl -> [%tcall beta depth (hd::sub) t' tl]
 | _ ->
    let t' = subst depth sub t in
    [%spy "subst-result" (ppterm depth [] 0 empty_env) t'];
    match args with
    | [] -> t'
    | ahd::atl ->
         match t' with
         | Const c -> App (c,ahd,atl)
         | Arg _
         | AppArg _ -> anomaly "beta takes only heap terms"
         | App (c,arg,args1) -> App (c,arg,args1@args)
         | Builtin (c,args1) -> Builtin (c,args1@args)
         | UVar (r,n,m) -> begin
            try UVar(r,n,m + in_fragment (n+m) args)
            with NotInTheFragment ->
              let args1 = C.mkinterval n m 0 in
              AppUVar (r,n,args1@args) end
         | AppUVar (r,depth,args1) -> AppUVar (r,depth,args1@args)
         | Lam _ -> anomaly "beta: some args and some lambdas"
         | CData x -> type_error (Printf.sprintf "beta: '%s'" (CData.show x))
         | Nil -> type_error "beta: Nil"
         | Cons _ -> type_error "beta: Cons"
         | Discard -> type_error "beta: Discard"
 end]

(* eat_args n [n ; ... ; n+k] (Lam_0 ... (Lam_k t)...) = n+k+1,[],t
   eat_args n [n ; ... ; n+k]@l (Lam_0 ... (Lam_k t)...) =
     n+k+1,l,t if t != Lam or List.hd l != n+k+1 *)
and eat_args depth l t =
  match t with
  | Lam t' when l > 0 -> eat_args (depth+1) (l-1) t'
  | UVar ({contents=t},origdepth,args) when t != C.dummy ->
     eat_args depth l (deref_uv ~from:origdepth ~to_:depth args t)
  | AppUVar  ({contents=t},origdepth,args) when t != C.dummy ->
     eat_args depth l (deref_appuv ~from:origdepth ~to_:depth args t)
  | _ -> depth,l,t

(* CSC: The following set of comments are to be revised. I found them scattered
   around and they refer to old names. They are also somehow duplicated *)
(* Deref is to be called only on heap terms and with from <= to *)
(* Deref is to be called only on heap terms and with from <= to
*  The args must live in to_.
*)
(* deref_uv performs lifting only and with from <= to
   if called on non-heap terms, it does not turn them to heap terms
   (if from=to_)

   Note:
     when deref_uv is called inside restrict, it may be from > to_
     t lives in from; args already live in to_
*)
   
and deref_appuv ?avoid ~from ~to_ args t =
  beta to_ [] (deref_uv ?avoid ~from ~to_ 0 t) args

and deref_uv ?avoid ~from ~to_ args t =
  [%trace "deref_uv" ("from:%d to:%d %a @@ %d"
      from to_ (ppterm from [] 0 empty_env) t args) begin
 if args == 0 then hmove ?avoid ~from ~to_ t
 else (* O(1) reduction fragment tested here *)
   let from,args',t = eat_args from args t in
   let t = deref_uv ?avoid ~from ~to_ 0 t in
   if args' == 0 then t
   else
     match t with
     | Lam _ -> anomaly "eat_args went crazy"
     | Const c ->
        let args = C.mkinterval (from+1) (args'-1) 0 in
        App (c,mkConst from, args)
     | App (c,arg,args2) ->
        let args = C.mkinterval from args' 0 in
        App (c,arg,args2 @ args)
     | Builtin (c,args2) ->
        let args = C.mkinterval from args' 0 in
        Builtin (c,args2 @ args)
     (* TODO: when the UVar/Arg is not C.dummy, we call deref_uv that
        will call move that will call_deref_uv again. Optimize the
        path *)
     | UVar(t,depth,args2) when from = depth+args2 ->
        UVar(t,depth,args2+args')
     | AppUVar (r,depth,args2) ->
        let args = C.mkinterval from args' 0 in
        AppUVar (r,depth,args2 @ args)
     | UVar (r,vardepth,argsno) ->
        let args1 = C.mkinterval vardepth argsno 0 in
        let args2 = C.mkinterval from args' 0 in
        let args = args1 @ args2 in
        AppUVar (r,vardepth,args)
     | Cons _ | Nil -> type_error "deref_uv: applied list"
     | Discard -> type_error "deref_uv: applied Discard"
     | CData _ -> t
     | Arg _ | AppArg _ -> assert false (* Uv gets assigned only heap term *)
  end]

;;

(* }}} *)

(* {{{ ************** unification ******************************* *)

(* is_flex is to be called only on heap terms *)
let rec is_flex ~depth =
 function
  | Arg _ | AppArg _ -> anomaly "is_flex called on Args"
  | UVar ({ contents = t }, vardepth, args) when t != C.dummy ->
     is_flex ~depth (deref_uv ~from:vardepth ~to_:depth args t)
  | AppUVar ({ contents = t }, vardepth, args) when t != C.dummy -> 
     is_flex ~depth (deref_appuv ~from:vardepth ~to_:depth args t)
  | UVar (r, _, _) | AppUVar (r, _, _) -> Some r
  | Const _ | Lam _ | App _ | Builtin _ | CData _ | Cons _ | Nil | Discard -> None

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
   heap = ?

   Note about dereferencing UVar(r,origdepth,args):
   - args live *here* (a/bdepth + depth)
   - !!r lives in origdepth
   + we deref_uv to move everything to a/bdepth + depth
   
   Note about dereferencing Arg(i,args):
   - args live *here* (bdepth + depth)
   - e.(i) lives in bdepth
   + we deref_uv to move everything to adepth + depth
*)


(* Tests is args are in the L_\lambda fragment and produces a map from
 *  constants to int.  The idea being that an UVar of level lvl also sees
 *  all the constants in the map, and the associated int is their position
 *  in the list of arguments starting from 0 *)
let is_llam lvl args adepth bdepth depth left e =
  let to_ = if left then adepth+depth else bdepth+depth in
  let get_con = function Const x -> x | _ -> raise RestrictionFailure in
  let deref_to_const = function
    | UVar ({ contents = t }, from, args) when t != C.dummy ->
        get_con (deref_uv ~from ~to_ args t)
    | AppUVar ({ contents = t }, from, args) when t != C.dummy -> 
        get_con (deref_appuv ~from ~to_ args t)
    | Arg (i,args) when e.(i) != C.dummy ->
        get_con (deref_uv ~from:adepth ~to_ args e.(i))
    | AppArg (i,args) when e.(i) != C.dummy -> 
        get_con (deref_appuv ~from:adepth ~to_ args e.(i))
    | Const x -> if not left && x >= bdepth then x + (adepth-bdepth) else x
    | _ -> raise RestrictionFailure
  in
  let rec aux n = function
    | [] -> []
    | x :: xs ->
       if x >= lvl && not (List.mem x xs) then (x,n) :: aux (n+1) xs
       else raise RestrictionFailure in
  try true, aux 0 (List.map deref_to_const args)
  with RestrictionFailure -> false, []
let is_llam lvl args adepth bdepth depth left e =
  let res = is_llam lvl args adepth bdepth depth left e in
  [%spy "is_llam" (fun fmt (b,map) -> Fmt.fprintf fmt "%d + %a = %b, %a"
    lvl (pplist (ppterm adepth [] bdepth e) " ") args b
    (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%d |-> %d" x n) " ") map) res];
  res

let rec mknLam n t = if n = 0 then t else mknLam (n-1) (Lam t)

(* [bind r args ... t] generates a term \args.t' to be assigned to r.
 * r is the variable being assigned
 * gamma is the level of the variable we assigning
 * l is its extended domain as a map (see is_llam)
 * a is adepth
 * b is bdepth
 * d is depth (local lamdas traversed during unif
 *   w is the same but during bind, hence current depth is (d+w)
 * delta is (a-b)
 * left is true when the variable being assigned is on the left (goal)
 * t is the term we are assigning to r
 * e is the env for args *)
let bind r gamma l a d delta b left t e =
  let new_lams = List.length l in
  let pos x = try List.assoc x l with Not_found -> raise RestrictionFailure in
  (* hmove = false makes the code insensitive to left/right, i.e. no hmove from b
   * to a is performed *)
  let cst ?(hmove=true) c b delta = (* The complex thing (DBL) *)
    if left then begin
      if c < gamma && c < b then c
      else
        let c = if hmove && c >= b then c + delta else c in
        if c < gamma then c
        else if c >= a + d then c + new_lams - (a+d - gamma)
        else pos c + gamma
    end else begin
      if c < gamma then c
      else if c >= a + d then c + new_lams - (a+d - gamma)
      else pos c + gamma
    end in
  let cst ?hmove c b delta =
    let n = cst ?hmove c b delta in
    [%spy "cst" (fun fmt (n,m) -> Fmt.fprintf fmt
      "%d -> %d (c:%d b:%d gamma:%d delta:%d d:%d)" n m c b gamma delta d)
      (c,n)];
    n in
  let rec bind b delta w t =
    [%trace "bind" ("%b gamma:%d + %a = t:%a a:%d delta:%d d:%d w:%d b:%d"
        left gamma (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%a |-> %d"
        (ppterm a [] b e) (mkConst x) n) " ") l
        (ppterm a [] b empty_env) t a delta d w b) begin
    match t with
    | UVar (r1,_,_) | AppUVar (r1,_,_) when r == r1 -> raise RestrictionFailure
    | Const c -> let n = cst c b delta in if n < 0 then mkConst n else Const n
    | Lam t -> Lam (bind b delta (w+1) t)
    | App (c,t,ts) -> App (cst c b delta, bind b delta w t, List.map (bind b delta w) ts)
    | Cons(hd,tl) -> Cons(bind b delta w hd, bind b delta w tl)
    | Nil -> t
    | Discard -> t
    | Builtin (c, tl) -> Builtin(c, List.map (bind b delta w) tl)
    | CData _ -> t
    (* deref_uv *)
    | Arg (i,args) when e.(i) != C.dummy ->
        bind a 0 w (deref_uv ~from:a ~to_:(a+d+w) args e.(i))
    | AppArg (i,args) when e.(i) != C.dummy ->
        bind a 0 w (deref_appuv ~from:a ~to_:(a+d+w) args e.(i))
    | UVar ({ contents = t }, from, args) when t != C.dummy ->
        bind b delta w (deref_uv ~from ~to_:((if left then b else a)+d+w) args t)
    | AppUVar ({ contents = t }, from, args) when t != C.dummy ->
        bind b delta w (deref_appuv ~from ~to_:((if left then b else a)+d+w) args t)
    (* pruning *)
    | (UVar _ | AppUVar _ | Arg _ | AppArg _) as orig ->
        (* We deal with all flexible terms in a uniform way *)
        let r, lvl, (is_llam, args), orig_args = match orig with
          | UVar(r,lvl,0) -> r, lvl, (true, []), []
          | UVar(r,lvl,args) ->
              let r' = oref C.dummy in
              let v = UVar(r',lvl+args,0) in
              r @:= mknLam args v;
              r', (lvl+args),  (true,[]), []
          | AppUVar (r,lvl, orig_args) ->
              r, lvl, is_llam lvl orig_args a b (d+w) left e, orig_args
          | Arg (i,0) ->
              let r = oref C.dummy in
              let v = UVar(r,a,0) in
              e.(i) <- v;
              r, a, (true,[]), []
          | Arg (i,args) ->
              let r = oref C.dummy in
              let v = UVar(r,a,0) in
              e.(i) <- v;
              let r' = oref C.dummy in
              let v' = UVar(r',a+args,0) in
              r @:= mknLam args v';
              r', a+args, (true, []), []
          | AppArg (i,orig_args) ->
              let is_llam, args = is_llam a orig_args a b (d+w) false e in
              let r = oref C.dummy in
              let v = UVar(r,a,0) in
              e.(i) <- v;
              r, a, (is_llam, args), orig_args
          | _ -> assert false in
        [%spy "bind-maybe-prune" (fun fmt () ->
           Fmt.fprintf fmt "lvl:%d is_llam:%b args:%a orig_args:%a orig:%a"
             lvl is_llam 
             (pplist (fun fmt (x,n) ->
                Fmt.fprintf fmt "%a->%d" (ppterm a [] b e) (mkConst x) n) " ") args
             (pplist (ppterm a [] b e) " ") orig_args
             (ppterm a [] b e) orig) ()];
        if is_llam then begin
          let n_args = List.length args in
          if lvl > gamma then
            (* All orig args go away, but some between gamma and lvl can stay
             * if they are in l or locally bound [d,w] *)
            let args_gamma_lvl_abs, args_gamma_lvl_here =
              let mk_arg i = mkConst i, mkConst (cst ~hmove:false i b delta) in
              let rec mk_interval d argsno n =
                if n = argsno then []
                else if n+d >= lvl then
                 let i = n+d in
                 (* cut&paste from below *)
                 (try
                   let nn = List.assoc i args in
                   (mkConst (lvl+nn), mkConst (gamma+List.length l+n)) :: mk_interval d argsno (n+1)
                  with Not_found -> mk_interval d argsno (n+1))
                else mk_arg (n+d)::mk_interval d argsno (n+1) in
              let rec keep_cst_for_lvl = function
                | [] ->
                   mk_interval (d + if left then a else b) w 0
                | (i,mm) :: rest ->
                    if i < lvl then (
                     mk_arg i :: keep_cst_for_lvl rest
                    ) else
                     (try
                       let nn = List.assoc i args in
                       (mkConst (lvl+nn), mkConst mm) :: keep_cst_for_lvl rest
                      with Not_found -> keep_cst_for_lvl rest) in
              List.split (keep_cst_for_lvl (List.sort Pervasives.compare l)) in
            let r' = oref C.dummy in
            r @:= mknLam n_args (mkAppUVar r' gamma args_gamma_lvl_abs);
            mkAppUVar r' gamma args_gamma_lvl_here
          else
            (* given that we need to make lambdas to prune some args,
             * we also permute to make the restricted meta eventually
             * fall inside the small fragment (sort the args) *)
            let args = List.sort Pervasives.compare args in
            let args_lvl, args_here =
              List.fold_right (fun (c, c_p) (a_lvl, a_here as acc) ->
                try
                  let i =
                    if c < gamma then c
                    else if c >= (if left then b else a) + d then c + new_lams - (a+d - gamma)
                    else pos c + gamma in
                  mkConst (c_p + lvl) :: a_lvl,
                  mkConst i :: a_here
                with RestrictionFailure -> acc) args ([],[]) in
            if n_args = List.length args_here then
              (* no pruning, just binding the args as a normal App *)
              mkAppUVar r lvl (List.map (bind b delta w) orig_args)
            else
              (* we need to project away some of the args *)
              let r' = oref C.dummy in
              let v = mkAppUVar r' lvl args_lvl in
              r @:= mknLam n_args v;
              (* This should be the beta reduct. One could also
               * return the non reduced but bound as in the other if branch *)
              mkAppUVar r' lvl args_here
        end else begin
          mkAppUVar r lvl (List.map (bind b delta w) orig_args)
        end
  end] in
  try
    let v = mknLam new_lams (bind b delta 0 t) in
    [%spy "assign(HO)" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
        (uppterm gamma [] a e) (UVar(r,gamma,0))
        (uppterm gamma [] a e) v) ()];
    r @:= v;
    true
  with RestrictionFailure -> [%spy "bind result" (fun fmt x -> Fmt.fprintf fmt "%b" x) false];false
;;
(* exception Non_linear *)

let rec list_to_lp_list = function
  | [] -> Nil
  | x::xs -> Cons(x,list_to_lp_list xs)
;;

let delay_hard_unif_problems = Fork.new_local false
let error_msg_hard_unif a b =
  "Unification problem outside the pattern fragment. ("^
  show_term a^
  " == " ^
  show_term b^
  ") Pass -delay-problems-outside-pattern-fragment (elpi command line utility) "^
  "or set delay_outside_fragment to true (Elpi_API) in order to delay "^
  "(deprecated, for Teyjus compatibility)."

let rec unif matching depth adepth a bdepth b e =
   [%trace "unif" ("@[<hov 2>^%d:%a@ =%d%s= ^%d:%a@]%!"
       adepth (ppterm (adepth+depth) [] adepth empty_env) a
       depth (if matching then "m" else "")
       bdepth (ppterm (bdepth+depth) [] adepth e) b)
   begin let delta = adepth - bdepth in
   (delta = 0 && a == b) || match a,b with
    | (Discard, _ | _, Discard) -> true
  
   (* _ as X binding *)
   | _, App(c,arg,[(Arg _ | AppArg _) as as_this]) when c == C.asc ->
      unif matching depth adepth a bdepth arg e &&
      unif matching depth adepth a bdepth as_this e 
   | _, App(c,arg,_) when c == C.asc -> error "syntax error in as"
   | App(c,arg,_), _ when c == C.asc ->
      unif matching depth adepth arg bdepth b e

(* TODO: test if it is better to deref_uv first or not, i.e. the relative order
   of the clauses below *)
   | UVar(r1,_,args1), UVar(r2,_,args2)
     when r1 == r2 && !!r1 == C.dummy -> args1 == args2
   | AppUVar(r1,_,xs), AppUVar(r2,_,ys)
     when r1 == r2 && !!r1 == C.dummy-> 
       for_all2 (fun x y -> unif matching depth adepth x bdepth y e) xs ys

   (* deref_uv *)
   | UVar ({ contents = t }, from, args), _ when t != C.dummy ->
      unif matching depth adepth (deref_uv ~from ~to_:(adepth+depth) args t) bdepth b e
   | AppUVar ({ contents = t }, from, args), _ when t != C.dummy -> 
      unif matching depth adepth (deref_appuv ~from ~to_:(adepth+depth) args t) bdepth b e
   | _, UVar ({ contents = t }, from, args) when t != C.dummy ->
      unif matching depth adepth a bdepth (deref_uv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, AppUVar ({ contents = t }, from, args) when t != C.dummy ->
      unif matching depth adepth a bdepth (deref_appuv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, Arg (i,args) when e.(i) != C.dummy ->
(*        if matching then raise Non_linear; *)
      (* XXX BROKEN deref_uv invariant XXX
       *   args not living in to_ but in bdepth+depth *)
      unif matching depth adepth a adepth
        (deref_uv ~from:adepth ~to_:(adepth+depth) args e.(i)) empty_env
   | _, AppArg (i,args) when e.(i) != C.dummy -> 
(*        if matching then raise Non_linear; *)
      (* XXX BROKEN deref_uv invariant XXX
       *   args not living in to_ but in bdepth+depth
       *   NOTE: the map below has been added after the XXX, but
           I believe it is wrong as well *)
      let args =
       List.map (move ~adepth ~from:bdepth ~to_:adepth e) args in
      unif matching depth adepth a adepth
        (deref_appuv ~from:adepth ~to_:(adepth+depth) args e.(i)) empty_env

   (* UVar introspection (matching) *)
   | (UVar _ | AppUVar _), Const c when c == C.uvarc && matching -> true
   | UVar(r,vd,ano), App(c,hd,[]) when c == C.uvarc && matching ->
      unif matching depth adepth (UVar(r,vd,ano)) bdepth hd e
   | AppUVar(r,vd,_), App(c,hd,[]) when c == C.uvarc && matching ->
      unif matching depth adepth (UVar(r,vd,0)) bdepth hd e
   | UVar(r,vd,ano), App(c,hd,[arg]) when c == C.uvarc && matching ->
      let r_exp = oref C.dummy in
      let exp = UVar(r_exp,0,0) in
      r @:= UVar(r_exp,0,vd);
      unif matching depth adepth exp bdepth hd e &&
      let args = list_to_lp_list (C.mkinterval 0 (vd+ano) 0) in
      unif matching depth adepth args bdepth arg e
   | AppUVar(r,vd,args), App(c,hd,[arg]) when c == C.uvarc && matching ->
      let r_exp = oref C.dummy in
      let exp = UVar(r_exp,0,0) in
      r @:= UVar(r_exp,0,vd);
      unif matching depth adepth exp bdepth hd e &&
      let args = list_to_lp_list (C.mkinterval 0 vd 0 @ args) in
      unif matching depth adepth args bdepth arg e
   | _, (Const c | App(c,_,[])) when c == C.uvarc && matching -> false
   (* On purpose we let the fully applied uvarc pass, so that at the
    * meta level one can unify fronzen constants. One can use the var builtin
    * to discriminate the two cases, as in "p (uvar F L as X) :- var X, .." *)

   (* assign *)
   | _, Arg (i,0) ->
     begin try
      let v = hmove ~from:(adepth+depth) ~to_:adepth a in
      [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
          (uppterm adepth [] adepth e) b (uppterm adepth [] adepth e) v) ()];
      e.(i) <- v;
      true
     with RestrictionFailure -> false end
   | UVar({ rest = [] },_,0), UVar ({ rest = _ :: _ },_,0) -> unif matching depth bdepth b adepth a e
   | AppUVar({ rest = [] },_,_), UVar ({ rest = _ :: _ },_,0) -> unif matching depth bdepth b adepth a e
   | _, UVar (r,origdepth,0) ->
       begin try
         let t =
           if depth = 0 then
             hmove ~avoid:r ~from:adepth ~to_:origdepth a
           else
             (* First step: we lift the l.h.s. to the r.h.s. level *)
             let a = hmove ~avoid:r ~from:(adepth+depth) ~to_:(bdepth+depth) a in
             (* Second step: we restrict the l.h.s. *)
             hmove ~from:(bdepth+depth) ~to_:origdepth a in
         [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
           (uppterm depth [] bdepth e) b
           (uppterm depth [] bdepth e) t) ()];
         r @:= t;
         true
       with RestrictionFailure -> false end
   | UVar (r,origdepth,0), _ when not matching ->
       begin try
         let t =
           if depth=0 then
             move ~avoid:r ~adepth ~from:bdepth ~to_:origdepth e b
           else
             (* First step: we lift the r.h.s. to the l.h.s. level *)
             let b = move ~avoid:r ~adepth ~from:(bdepth+depth) ~to_:(adepth+depth) e b in
             (* Second step: we restrict the r.h.s. *)
             hmove ~from:(adepth+depth) ~to_:origdepth b in
         [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
           (uppterm origdepth [] 0 empty_env) a
           (uppterm origdepth [] 0 empty_env) t) ()];
         r @:= t;
         true
       with RestrictionFailure -> false end

   (* simplify *)
   (* TODO: unif matching->deref_uv case. Rewrite the code to do the job directly? *)
   | _, Arg (i,args) ->
      let v = fst (make_lambdas adepth args) in
      [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
        (uppterm depth [] bdepth e) (Arg(i,0))
        (uppterm depth [] bdepth e) v) ()];
      e.(i) <- v;
      [%spy "assign" (ppterm depth [] adepth empty_env) (e.(i))];
      unif matching depth adepth a bdepth b e
   | UVar({ rest = [] },_,a1), UVar ({ rest = _ :: _ },_,a2) when a1 + a2 > 0 -> unif matching depth bdepth b adepth a e
   | AppUVar({ rest = [] },_,_), UVar ({ rest = _ :: _ },_,a2) when  a2 > 0 -> unif matching depth bdepth b adepth a e
   | _, UVar (r,origdepth,args) when args > 0 ->
      let v = fst (make_lambdas origdepth args) in
      [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
        (uppterm depth [] bdepth e) (UVar(r,origdepth,0))
        (uppterm depth [] bdepth e) v) ()];
      r @:= v;
      unif matching depth adepth a bdepth b e
   | UVar (r,origdepth,args), _ when args > 0 ->
      let v = fst (make_lambdas origdepth args) in
      [%spy "assign" (fun fmt _ -> Fmt.fprintf fmt "%a := %a"
         (uppterm depth [] adepth e) (UVar(r,origdepth,0))
         (uppterm depth [] adepth e) v) ()];
      r @:= v;
      unif matching depth adepth a bdepth b e

   (* HO *)
   | other, AppArg(i,args) ->
       let is_llam, args = is_llam adepth args adepth bdepth depth false e in
       if is_llam then
         let r = oref C.dummy in
         e.(i) <- UVar(r,adepth,0);
         bind r adepth args adepth depth delta bdepth false other e
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth e) b ;
       let r = oref C.dummy in
       e.(i) <- UVar(r,adepth,0);
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers =
         match is_flex (adepth+depth) other with
         | None -> [r]
         | Some r' -> if r==r' then [r] else [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else error (error_msg_hard_unif a b)
   | AppUVar({ rest = _ :: _ },_,_), (AppUVar ({ rest = [] },_,_) | UVar ({ rest = [] },_,_)) -> unif matching depth bdepth b adepth a e
   | AppUVar (r, lvl,args), other when not matching ->
       let is_llam, args = is_llam lvl args adepth bdepth depth true e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth true other e
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth empty_env) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers = match is_flex (bdepth+depth) other with | None -> [r] | Some r' -> [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else error (error_msg_hard_unif a b)
   | other, AppUVar (r, lvl,args) ->
       let is_llam, args = is_llam lvl args adepth bdepth depth false e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth false other e
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth e) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers =
         match is_flex (adepth+depth) other with
         | None -> [r]
         | Some r' -> if r==r' then [r] else [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else error (error_msg_hard_unif a b)
  
   (* recursion *)
   | App (c1,x2,xs), App (c2,y2,ys) ->
      (* Compressed cut&past from Const vs Const case below +
         delta=0 optimization for <c1,c2> and <x2,y2> *)
      ((delta=0 || c1 < bdepth) && c1=c2
       || c1 >= adepth && c1 = c2 + delta)
       &&
       (delta=0 && x2 == y2 || unif matching depth adepth x2 bdepth y2 e) &&
       for_all2 (fun x y -> unif matching depth adepth x bdepth y e) xs ys
   | Builtin (c1,xs), Builtin (c2,ys) ->
       (* Inefficient comparison *)
       c1 = c2 && for_all2 (fun x y -> unif matching depth adepth x bdepth y e) xs ys
   | Lam t1, Lam t2 -> unif matching (depth+1) adepth t1 bdepth t2 e
   | Const c1, Const c2 ->
      if c1 < bdepth then c1=c2 else c1 >= adepth && c1 = c2 + delta
   (*| Const c1, Const c2 when c1 < bdepth -> c1=c2
     | Const c, Const _ when c >= bdepth && c < adepth -> false
     | Const c1, Const c2 when c1 = c2 + delta -> true*)
   | CData d1, CData d2 -> CData.equal d1 d2
   | Cons(hd1,tl1), Cons(hd2,tl2) -> 
       unif matching depth adepth hd1 bdepth hd2 e && unif matching depth adepth tl1 bdepth tl2 e
   | Nil, Nil -> true

   (* eta *)
   | Lam t, Const c ->
       let extra = mkConst (bdepth+depth) in
       let eta = App(c,extra,[]) in
       unif matching (depth+1) adepth t bdepth eta e
   | Const c, Lam t ->
       let extra = mkConst (adepth+depth) in
       let eta = App(c,extra,[]) in
       unif matching (depth+1) adepth eta bdepth t e
   | Lam t, App (c,x,xs) ->
       let extra = mkConst (bdepth+depth) in
       let motion = move ~adepth ~from:(bdepth+depth) ~to_:(bdepth+depth+1) e in
       let x = motion x in
       let xs = List.map motion xs @ [extra] in
       let eta = App(c,x,xs) in
       unif matching (depth+1) adepth t bdepth eta e
   | App (c,x,xs), Lam t ->
       let extra = mkConst (adepth+depth) in
       let motion = hmove ~from:(bdepth+depth) ~to_:(bdepth+depth+1) in
       let x = motion x in
       let xs = List.map motion xs @ [extra] in
       let eta = App(c,x,xs) in
       unif matching (depth+1) adepth eta bdepth t e

   | _ -> false
   end]
;;

(* FISSA PRECEDENZA PER AS e FISSA INDEXING per AS e fai coso generale in unif *)

let unif ~matching adepth e bdepth a b =
 let res = unif matching 0 adepth a bdepth b e in
 [%spy "unif result" (fun fmt x -> Fmt.fprintf fmt "%b" x) res];
 [%spyif "select" (not res) (fun fmt op ->
     Fmt.fprintf fmt "@[<hov 2>fail to %s: %a@ with %a@]" op
       (ppterm (adepth) [] adepth empty_env) a
       (ppterm (bdepth) [] adepth e) b)
     (if matching then "match" else "unify")];
 res
;;

(* Look in Git for Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower. *)

(* }}} *)

let rec deref_head ~depth = function
  | UVar ({ contents = t }, from, ano)
    when t != C.dummy ->
      deref_head ~depth (deref_uv ~from ~to_:depth ano t)
  | AppUVar ({contents = t}, from, args)
    when t != C.dummy ->
      deref_head ~depth (deref_appuv ~from ~to_:depth args t)
  | x -> x

let full_deref ~adepth env ~depth t =
  let rec deref d = function
  | Const _ as x -> x
  | Lam r -> Lam (deref (d+1) r)
  | App (n,x,xs) -> App(n, deref d x, List.map (deref d) xs)
  | Cons(hd,tl) -> Cons(deref d hd, deref d tl)
  | Nil as x -> x
  | Discard as x -> x
  | Arg (i,ano) when env.(i) != C.dummy ->
      deref d (deref_uv ~from:adepth ~to_:d ano env.(i))
  | Arg _ as x -> x
  | AppArg (i,args) when env.(i) != C.dummy ->
      deref d (deref_appuv ~from:adepth ~to_:d args env.(i))
  | AppArg (i,args) -> AppArg (i, List.map (deref d) args)
  | UVar (r,lvl,ano) when !!r != C.dummy ->
      deref d (deref_uv ~from:lvl ~to_:d ano !!r)
  | UVar _ as x -> x
  | AppUVar (r,lvl,args) when !!r != C.dummy ->
      deref d (deref_appuv ~from:lvl ~to_:d args !!r)
  | AppUVar (r,lvl,args) -> AppUVar (r,lvl,List.map (deref d) args)
  | Builtin(c,xs) -> Builtin(c,List.map (deref d) xs)
  | CData _ as x -> x
  in
    deref depth t

type assignment = uvar_body * int * term

let expand_uv r ~lvl ~ano =
  let args = C.mkinterval 0 (lvl+ano) 0 in
  if lvl = 0 then AppUVar(r,lvl,args), None else
  let r1 = oref C.dummy in
  let t = AppUVar(r1,0,args) in
  let assignment = mknLam ano t in
  t, Some (r,lvl,assignment)
let expand_uv ~depth r ~lvl ~ano =
  [%spy "expand-uv-in" (fun fmt t ->
    Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env) t) (UVar(r,lvl,ano))];
  let t, ass as rc = expand_uv r ~lvl ~ano in
  [%spy "expand-uv-out" (fun fmt t ->
    Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env) t) t];
  [%spy "expand-uv-out" (fun fmt -> function
    | None -> Fmt.fprintf fmt "no assignment"
    | Some (_,_,t) ->
        Fmt.fprintf fmt "%a := %a"
          (uppterm depth [] 0 empty_env) (UVar(r,lvl,ano))
          (uppterm lvl [] 0 empty_env) t) ass];
  rc

let expand_appuv r ~lvl ~args =
  if lvl = 0 then AppUVar(r,lvl,args), None else
  let args_lvl = C.mkinterval 0 lvl 0 in
  let r1 = oref C.dummy in
  let t = AppUVar(r1,0,args_lvl @ args) in
  let nargs = List.length args in
  let assignment =
    mknLam nargs (AppUVar(r1,0,args_lvl @ C.mkinterval lvl nargs 0)) in
  t, Some (r,lvl,assignment)
let expand_appuv ~depth r ~lvl ~args =
  [%spy "expand-appuv-in" (fun fmt t ->
    Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env) t) (AppUVar(r,lvl,args))];
  let t, ass as rc = expand_appuv r ~lvl ~args in
  [%spy "expand-appuv-out" (fun fmt t ->
    Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env) t) t];
  [%spy "expand-uv-out" (fun fmt -> function
    | None -> Fmt.fprintf fmt "no assignment"
    | Some (_,_,t) ->
        Fmt.fprintf fmt "%a := %a"
          (uppterm depth [] 0 empty_env) (AppUVar(r,lvl,args))
          (uppterm lvl [] 0 empty_env) t) ass];
  rc


let shift_bound_vars ~depth ~to_ t =
  let shift_db d n =
    if n < depth then n
    else n + to_ - depth in
  let rec shift d = function
  | Const n as x -> let m = shift_db d n in if m = n then x else  mkConst m
  | Lam r -> Lam (shift (d+1) r)
  | App (n,x,xs) ->
      App(shift_db d n, shift d x, List.map (shift d) xs)
  | Cons(hd,tl) -> Cons(shift d hd, shift d tl)
  | Nil as x -> x
  | Discard as x -> x
  | Arg _ as x -> x
  | AppArg (i,args) -> AppArg (i, List.map (shift d) args)
  | (UVar (r,_,_) | AppUVar(r,_,_)) when !!r != C.dummy ->
      anomaly "shift_bound_vars: non-derefd term"
  | UVar _ as x -> x
  | AppUVar (r,lvl,args) -> AppUVar (r,lvl,List.map (shift d) args)
  | Builtin(c,xs) -> Builtin(c,List.map (shift d) xs)
  | CData _ as x -> x
  in
    if depth = to_ then t else shift depth t

let subtract_to_consts ~amount ~depth t =
  let shift_db d n =
    if n < 0 then n
    else if n < amount then
      error "The term cannot be put in the desired context"
    else n - amount in
  let rec shift d = function
  | Const n as x -> let m = shift_db d n in if m = n then x else  mkConst m
  | Lam r -> Lam (shift (d+1) r)
  | App (n,x,xs) ->
      App(shift_db d n, shift d x, List.map (shift d) xs)
  | Cons(hd,tl) -> Cons(shift d hd, shift d tl)
  | Nil as x -> x
  | Discard as x -> x
  | Arg _ as x -> x
  | AppArg (i,args) -> AppArg (i, List.map (shift d) args)
  | (UVar (r,_,_) | AppUVar(r,_,_)) when !!r != C.dummy ->
      anomaly "subtract_to_consts: non-derefd term"
  | (UVar _ | AppUVar _) ->
      error "The term cannot be put in the desired context (leftover uvar)"
  | Builtin(c,xs) -> Builtin(c,List.map (shift d) xs)
  | CData _ as x -> x
  in
    if amount = 0 then t else shift 0 t

end
(* }}} *)
open HO

let _ = do_deref := deref_uv;;
let _ = do_app_deref := deref_appuv;;

(******************************************************************************
  Indexing
 ******************************************************************************)

module Indexing = struct (* {{{ *)

let mustbevariablec = min_int (* uvar or uvar t or uvar l t *)

let ppclause f ~depth hd { args = args; hyps = hyps; } =
  Fmt.fprintf f "@[<hov 1>%s %a :- %a.@]" (C.show hd)
     (pplist (uppterm ~min_prec:(Parser.appl_precedence+1) depth [] depth empty_env) " ") args
     (pplist (uppterm ~min_prec:(Parser.appl_precedence+1) depth [] depth empty_env) ", ") hyps

let tail_opt = function
  | [] -> []
  | _ :: xs -> xs

let hd_opt = function
  | b :: _ -> b
  | _ -> false

type clause_arg_classification =
  | Variable
  | MustBeVariable
  | Rigid of constant * bool (* matching *)

let rec classify_clause_arg ~depth matching t =
  match deref_head ~depth t with
  | Const k when k == C.uvarc -> MustBeVariable
  | Const k -> Rigid(k,matching)
  | Nil -> Rigid (C.nilc,matching)
  | Cons _ -> Rigid (C.consc,matching)
  | App (k,_,_) when k == C.uvarc -> MustBeVariable
  | App (k,a,_) when k == C.asc -> classify_clause_arg ~depth matching a
  | (App (k,_,_) | Builtin (k,_)) -> Rigid (k,matching)
  | Lam _ -> Variable (* loose indexing to enable eta *)
  | Arg _ | UVar _ | AppArg _ | AppUVar _ | Discard -> Variable
  | CData d -> 
     let hash = -(CData.hash d) in
     if hash > mustbevariablec then Rigid (hash,matching)
     else Rigid (hash+1,matching)

let rec classify_clause_argno ~depth argno mode = function
  | [] -> Variable
  | x :: _ when argno == 0 -> classify_clause_arg ~depth (hd_opt mode) x
  | _ :: xs -> classify_clause_argno ~depth (argno-1) (tail_opt mode) xs

let dec_to_bin2 num =
  let rec aux x = 
    if x==1 then ["1"] else
    if x==0 then ["0"] else 
    if x mod 2 == 1 then "1" :: aux (x/2)
    else "0" :: aux (x/2)
  in
    String.concat "" (List.rev (aux num))

let hash_bits = Sys.int_size - 1 (* the sign *)

let hash_arg_list goal hd ~depth args mode spec =
  let nargs = List.(length (filter (fun x -> x > 0) spec)) in
  (* we partition equally, that may not be smart, but is simple ;-) *)
  let arg_size = hash_bits / nargs in
  let hash size k =
    let modulus = 1 lsl size in
    let kabs = Hashtbl.hash k in
    let h = kabs mod modulus in
    [%spy "subhash-const" (fun fmt () ->
       Fmt.fprintf fmt "%s: %s" (C.show k)
         (dec_to_bin2 h)) ()];
    h in
  let all_1 size = max_int lsr (hash_bits - size) in
  let all_0 size = 0 in
  let shift slot_size position x = x lsl (slot_size * position) in
  let rec aux off acc args mode spec =
    match args, spec with
    | _, [] -> acc
    | [], _ -> acc
    | x::xs, n::spec ->
         let h = aux_arg arg_size (hd_opt mode) n x in
         aux (off + arg_size) (acc lor (h lsl off)) xs (tail_opt mode) spec
  and aux_arg size matching deep arg =
    let h =
      match deref_head ~depth arg with
      | App (k,a,_) when k == C.asc -> aux_arg size matching deep a
      | Const k when k == C.uvarc ->
          hash size mustbevariablec
      | App(k,_,_) when k == C.uvarc && deep = 1 ->
          hash size mustbevariablec
      | Const k -> hash size k
      | App(k,_,_) when deep = 1 -> hash size k
      | App(k,x,xs) ->
          let size = size / (List.length xs + 2) in
          let self = aux_arg size matching (deep-1) in
          let shift = shift size in
          (hash size k) lor
          (shift 1 (self x)) lor
          List.(fold_left (lor) 0 (mapi (fun i x -> shift (i+2) (self x)) xs))
      | (UVar _ | AppUVar _) when matching && goal -> hash size mustbevariablec
      | (UVar _ | AppUVar _) when matching -> all_1 size
      | (UVar _ | AppUVar _) -> if goal then all_0 size else all_1 size
      | (Arg _ | AppArg _) -> all_1 size
      | Nil -> hash size C.nilc
      | Cons (x,xs) ->
          let size = size / 2 in
          let self = aux_arg size matching (deep-1) in
          let shift = shift size in
          (hash size C.consc) lor (shift 1 (self x))
      | CData s -> hash size (CData.hash s)
      | Lam _ -> all_1 size
      | Discard -> all_1 size
      | Builtin(k,xs) ->
          let size = size / (List.length xs + 1) in
          let self = aux_arg size matching (deep-1) in
          let shift = shift size in
          (hash size k) lor
          List.(fold_left (lor) 0 (mapi (fun i x -> shift (i+1) (self x)) xs))
    in
    [%spy "subhash" (fun fmt ->
       Fmt.fprintf fmt "%s: %d: %s: %a"
         (if goal then "goal" else "clause")
         size
         (dec_to_bin2 h)
         (uppterm depth [] 0 empty_env)) arg];
    h
  in
  let h = aux 0 0 args mode spec in
  [%spy "hash" (fun fmt ->
     Fmt.fprintf fmt "%s: %s: %a"
       (if goal then "goal" else "clause")
       (dec_to_bin2 h)
       (pplist ~boxed:true (uppterm depth [] 0 empty_env) " "))
      (Const hd :: args)];
  h

let hash_clause_arg_list = hash_arg_list false
let hash_goal_arg_list = hash_arg_list true

let add1clause ~depth m (predicate,clause) =
  match Ptmap.find predicate m with
  | TwoLevelIndex { all_clauses; argno; mode; flex_arg_clauses; arg_idx } ->
      (* X matches both rigid and flexible terms *)
      begin match classify_clause_argno ~depth argno mode clause.args with
      | Variable ->
        Ptmap.add predicate (TwoLevelIndex {
          argno; mode;
          all_clauses = clause :: all_clauses;
          flex_arg_clauses = clause :: flex_arg_clauses;
          arg_idx = Ptmap.map (fun l_rev -> clause :: l_rev) arg_idx;
        }) m
      | MustBeVariable ->
      (* uvar matches only flexible terms (or itself at the meta level) *)
        let l_rev =
          try Ptmap.find mustbevariablec arg_idx
          with Not_found -> flex_arg_clauses in
        Ptmap.add predicate (TwoLevelIndex {
            argno; mode;
          all_clauses = clause :: all_clauses;
          flex_arg_clauses;
          arg_idx = Ptmap.add mustbevariablec (clause::l_rev) arg_idx;
        }) m
      | Rigid (arg_hd,matching) ->
      (* a rigid term matches flexible terms only in unification mode *)
        let l_rev =
          try Ptmap.find arg_hd arg_idx
          with Not_found -> flex_arg_clauses in
        let all_clauses =
          if matching then all_clauses else clause :: all_clauses in
        Ptmap.add predicate (TwoLevelIndex {
            argno; mode;
          all_clauses;
          flex_arg_clauses;
          arg_idx = Ptmap.add arg_hd (clause::l_rev) arg_idx;
        }) m
      end
  | BitHash { mode; args; time; args_idx } ->
      let hash = hash_clause_arg_list predicate ~depth clause.args mode args in
      let clauses =
        try Ptmap.find hash args_idx
        with Not_found -> [] in
      Ptmap.add predicate (BitHash {
         mode; args;
         time = time + 1;
         args_idx = Ptmap.add hash ((clause,time) :: clauses) args_idx
       }) m
  | exception Not_found ->
      match classify_clause_argno ~depth 0 [] clause.args with
      | Variable ->
      Ptmap.add predicate (TwoLevelIndex {
        argno = 0; mode = [];
        all_clauses = [clause];
        flex_arg_clauses = [clause];
        arg_idx =Ptmap.empty;
      }) m
      | MustBeVariable ->
      Ptmap.add predicate (TwoLevelIndex {
        argno = 0;mode = [];
        all_clauses = [clause];
        flex_arg_clauses = [];
        arg_idx = Ptmap.add mustbevariablec [clause] Ptmap.empty;
      }) m
      | Rigid (arg_hd,matching) ->
      let all_clauses = if matching then [] else [clause] in
      Ptmap.add predicate (TwoLevelIndex {
        argno = 0;mode = [];
        all_clauses;
        flex_arg_clauses = [];
        arg_idx = Ptmap.add arg_hd [clause] Ptmap.empty;
      }) m

let add_clauses ~depth clauses p =       
  let p = List.fold_left (add1clause ~depth) p clauses in
  p

let make_index ~depth ~indexing p =
  let m = Constants.Map.fold (fun predicate (mode, indexing) m ->
    match indexing with
    | Hash args ->
      Ptmap.add predicate (BitHash {
        args;
        mode;
        time = min_int;
        args_idx = Ptmap.empty;
      }) m
    | MapOn argno ->
      Ptmap.add predicate (TwoLevelIndex {
        argno;
        mode;
        all_clauses = [];
        flex_arg_clauses = [];
        arg_idx = Ptmap.empty;
      }) m) indexing Ptmap.empty in
  let p = List.rev p in
  { index = add_clauses ~depth p m; src = [] }

let add_clauses ~depth clauses clauses_src { index; src } =
  { index = add_clauses ~depth clauses index; src = List.rev clauses_src @ src }

 
let predicate_of_goal ~depth t =
  match deref_head ~depth t with
  | Const k as x -> k, x
  | App (k,_,_) as x -> k, x
  | Builtin _ -> assert false
  | (Nil | Cons _ | Arg _ | AppArg _ | Lam _
    | UVar _ | AppUVar _ | CData _ | Discard) as x ->
    type_error ("The goal's head is not a predicate: " ^ show_term x)

type goal_arg_classification =
  | Variable
  | Rigid of constant

let rec classify_goal_arg ~depth t =
  match deref_head ~depth t with
  | Const k when k == C.uvarc -> Rigid mustbevariablec
  | Const k -> Rigid(k)
  | Nil -> Rigid (C.nilc)
  | Cons _ -> Rigid (C.consc)
  | App (k,_,_) when k == C.uvarc -> Rigid mustbevariablec
  | App (k,a,_) when k == C.asc -> classify_goal_arg ~depth a
  | (App (k,_,_) | Builtin (k,_)) -> Rigid (k)
  | Lam _ -> Variable (* loose indexing to enable eta *)
  | Arg _ | UVar _ | AppArg _ | AppUVar _ | Discard -> Variable
  | CData d -> 
     let hash = -(CData.hash d) in
     if hash > mustbevariablec then Rigid (hash)
     else Rigid (hash+1)

let classify_goal_argno ~depth argno = function
  | Const _ -> Variable
  | App(_,x,_) when argno == 0 -> classify_goal_arg ~depth x
  | App(_,_,xs) ->
      let x =
        try List.nth xs (argno-1)
        with Invalid_argument _ ->
          type_error ("The goal is not applied enough")
      in
      classify_goal_arg ~depth x
  | _ -> assert false

let hash_goal_args ~depth mode args goal =
  match goal with
  | Const _ -> 0
  | App(k,x,xs) -> hash_goal_arg_list k ~depth (x::xs) mode args
  | _ -> assert false

let get_clauses ~depth goal { index = m } =
 let predicate, goal = predicate_of_goal ~depth goal in
 let rc =
   try
     match Ptmap.find predicate m with
     | TwoLevelIndex { all_clauses; argno; mode; flex_arg_clauses; arg_idx } ->
       begin match classify_goal_argno ~depth argno goal with
       | Variable -> all_clauses
       | Rigid arg_hd ->
          try Ptmap.find arg_hd arg_idx
          with Not_found -> flex_arg_clauses
       end
     | BitHash { args; mode; args_idx } ->
       let hash = hash_goal_args ~depth mode args goal in
       let cl = List.flatten (Ptmap.find_unifiables hash args_idx) in
       List.(map fst (sort (fun (_,cl1) (_,cl2) -> cl2 - cl1) cl))
   with Not_found -> []
 in
 [%log "get_clauses" (Constants.show predicate) (List.length rc)];
 rc

(* flatten_snd = List.flatten o (List.map ~~snd~~) *)
(* TODO: is this optimization necessary or useless? *)
let rec flatten_snd =
 function
    [] -> []
  | (_,(hd,_,_))::tl -> hd @ flatten_snd tl 

let close_with_pis depth vars t =
 if vars = 0 then t
 else
  (* lifts the term by vars + replaces Arg(i,..) with x_{depth+i} *)
  let fix_const c = if c < depth then c else c + vars in
  (* TODO: the next function is identical to lift_pat, up to the
     instantiation of Args. The two codes should be unified *)
  let rec aux =
   function
    | Const c -> mkConst (fix_const c)
    | Arg (i,argsno) ->
       (match C.mkinterval (depth+vars) argsno 0 with
        | [] -> Const(i+depth)
        | [x] -> App(i+depth,x,[])
        | x::xs -> App(i+depth,x,xs))
    | AppArg (i,args) ->
       (match List.map aux args with
        | [] -> anomaly "AppArg to 0 args"
        | [x] -> App(i+depth,x,[])
        | x::xs -> App(i+depth,x,xs))
    | App(c,x,xs) -> App(fix_const c,aux x,List.map aux xs)
    | Builtin(c,xs) -> Builtin(c,List.map aux xs)
    | UVar(_,_,_) as orig ->
       (* TODO: quick hack here, but it does not work for AppUVar *)
       hmove ~from:depth ~to_:(depth+vars) orig
    | AppUVar(r,vardepth,args) ->
       assert false (* TODO, essentially almost copy the code from move delta < 0 *)
    | Cons(hd,tl) -> Cons(aux hd, aux tl)
    | Nil as x -> x
    | Discard as x -> x
    | Lam t -> Lam (aux t)
    | CData _ as x -> x
  in
  let rec add_pis n t =
   if n = 0 then t else App(C.pic,Lam (add_pis (n-1) t),[]) in
  add_pis vars (aux t)

let local_prog { src } =  src

end (* }}} *)

open Indexing

(* Used to pass the program to the CHR runtime *)
let orig_prolog_program = Fork.new_local (make_index ~depth:0 ~indexing:Constants.Map.empty [])

(******************************************************************************
  Dynamic Prolog program
 ******************************************************************************)

module Clausify : sig

  val clausify : prolog_prog -> depth:int -> term -> (constant*clause) list * clause_src list * int

  val clausify1 : loc:Loc.t -> mode C.Map.t -> nargs:int -> depth:int -> term -> (constant*clause) * clause_src * int
  
  (* Utilities that deref on the fly *)
  val lp_list_to_list : depth:int -> term -> term list
  val get_lambda_body : depth:int -> term -> term
  val split_conj      : depth:int -> term -> term list

end = struct  (* {{{ *)

let rec term_map m = function
  | Const x when List.mem_assoc x m -> mkConst (List.assoc x m)
  | Const _ as x -> x
  | App(c,x,xs) when List.mem_assoc c m ->
      App(List.assoc c m,term_map m x, smart_map (term_map m) xs)
  | App(c,x,xs) -> App(c,term_map m x, smart_map (term_map m ) xs)
  | Lam x -> Lam (term_map m x)
  | UVar _ as x -> x
  | AppUVar(r,lvl,xs) -> AppUVar(r,lvl,smart_map (term_map m) xs)
  | Arg _ as x -> x
  | AppArg(i,xs) -> AppArg(i,smart_map (term_map m) xs)
  | Builtin(c,xs) -> Builtin(c,smart_map (term_map m) xs)
  | Cons(hd,tl) -> Cons(term_map m hd, term_map m tl)
  | Nil as x -> x
  | Discard as x -> x
  | CData _ as x -> x

let rec split_conj ~depth = function
  | App(c, hd, args) when c == C.andc || c == C.andc2 ->
      split_conj ~depth hd @ List.(flatten (map (split_conj ~depth) args))
  | Nil -> []
  | Cons(x,xs) -> split_conj ~depth x @ split_conj ~depth xs
  | UVar ({ contents=g },from,args) when g != C.dummy ->
    split_conj ~depth (deref_uv ~from ~to_:depth args g)
  | AppUVar ({contents=g},from,args) when g != C.dummy -> 
    split_conj ~depth (deref_appuv ~from ~to_:depth args g)
  | Discard -> []
  | _ as f -> [ f ]
;;

let rec lp_list_to_list ~depth = function
  | Cons(hd, tl) -> hd :: lp_list_to_list ~depth tl
  | Nil -> []
  | UVar ({ contents=g },from,args) when g != C.dummy ->
    lp_list_to_list ~depth (deref_uv ~from ~to_:depth args g)
  | AppUVar ({contents=g},from,args) when g != C.dummy -> 
    lp_list_to_list ~depth (deref_appuv ~from ~to_:depth args g)
  | x -> error (Fmt.sprintf "%s is not a list" (show_term x))
;;

let rec get_lambda_body ~depth = function
 | UVar ({ contents=g },from,args) when g != C.dummy ->
    get_lambda_body ~depth (deref_uv ~from ~to_:depth args g)
 | AppUVar ({contents=g},from,args) when g != C.dummy -> 
    get_lambda_body ~depth (deref_appuv ~from ~to_:depth args g)
 | Lam b -> b
 | _ -> error "pi/sigma applied to something that is not a Lam"
;;

(* BUG: the following clause is rejected because (Z c d) is not
   in the fragment. However, once X and Y becomes arguments, (Z c d)
   enters the fragment. 
r :- (pi X\ pi Y\ q X Y :- pi c\ pi d\ q (Z c d) (X c d) (Y c)) => ... *)

(* Takes the source of an implication and produces the clauses to be added to
 * the program and the number of existentially quantified constants turned
 * into globals.
 *
 * Invariants:
 *  - lts is the number of lambdas crossed and it is always = List.length ts
 *  - lcs is the number of new constants to be generated because a sigma
 *    has been crossed
 *  - the argument lives in (depth+lts)
 *  - the clause will live in (depth+lcs)
 *)

let rec claux1 ?loc get_mode vars depth hyps ts lts lcs t =
  [%trace "clausify" ("%a %d %d %d %d\n%!"
      (ppterm (depth+lts) [] 0 empty_env) t depth lts lcs (List.length ts)) begin
  match t with
  | Discard -> error ?loc "ill-formed hypothetical clause: discard in head position"
  | App(c, g2, [g1]) when c == C.rimplc ->
     claux1 ?loc get_mode vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == C.rimplc -> error ?loc "ill-formed hypothetical clause"
  | App(c, g1, [g2]) when c == C.implc ->
     claux1 ?loc get_mode vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == C.implc -> error ?loc "ill-formed hypothetical clause"
  | App(c, arg, []) when c == C.sigmac ->
     let b = get_lambda_body ~depth:(depth+lts) arg in
     let args =
      List.rev (List.filter (function (Arg _) -> true | _ -> false) ts) in
     let cst =
      match args with
         [] -> Const (depth+lcs)
       | hd::rest -> App (depth+lcs,hd,rest) in
     claux1 ?loc get_mode vars depth hyps (cst::ts) (lts+1) (lcs+1) b
  | App(c, arg, []) when c == C.pic ->
     let b = get_lambda_body ~depth:(depth+lts) arg in
     claux1 ?loc get_mode (vars+1) depth hyps (Arg(vars,0)::ts) (lts+1) lcs b
  | App(c, _, _) when c == C.andc || c == C.andc2 ->
     error ?loc "Conjunction in the head of a clause is not supported"
  | Const _
  | App _ as g ->
     let hyps =
      List.(flatten (rev_map (fun (ts,g) ->
         let g = hmove ~from:(depth+lts) ~to_:(depth+lts+lcs) g in
         let g = subst depth ts g in
          split_conj ~depth:(depth+lcs) g
        ) hyps)) in
     let g = hmove ~from:(depth+lts) ~to_:(depth+lts+lcs) g in
     let g = subst depth ts g in
(*     Fmt.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
      (ppterm (depth+lcs) [] 0 empty_env) g
      (pplist (ppterm (depth+lcs) [] 0 empty_env) " , ")
      hyps ;*)
     let hd, args =
      match g with
         Const h -> h, []
       | App(h,x,xs) -> h, x::xs
       | Arg _ | AppArg _ -> assert false 
       | Lam _ | Builtin _ | CData _ -> assert false
       | UVar _ | AppUVar _ -> assert false
       | Cons _ | Nil | Discard -> assert false
     in
     let c = { depth = depth+lcs; args; hyps; mode = get_mode hd; vars } in
     [%spy "extra" (fun fmt -> ppclause fmt ~depth:(depth+lcs) hd) c];
     (hd,c), { hdepth = depth; hsrc = g }, lcs
  | UVar ({ contents=g },from,args) when g != C.dummy ->
     claux1 ?loc get_mode vars depth hyps ts lts lcs
       (deref_uv ~from ~to_:(depth+lts) args g)
  | AppUVar ({contents=g},from,args) when g != C.dummy -> 
     claux1 ?loc get_mode vars depth hyps ts lts lcs
       (deref_appuv ~from ~to_:(depth+lts) args g)
  | Arg _ | AppArg _ -> anomaly "claux1 called on non-heap term"
  | Builtin (c,_) ->
     error ?loc ("Declaring a clause for built in predicate " ^ Constants.show c)
  | (Lam _ | CData _ ) as x ->
     error ?loc ("Assuming a string or int or float or function:" ^ show_term x)
  | UVar _ | AppUVar _ -> error ?loc "Flexible hypothetical clause"
  | Nil | Cons _ -> error ?loc "ill-formed hypothetical clause"
  end]
   
let clausify { index } ~depth t =
  let get_mode x =
    match Ptmap.find x index with
    | TwoLevelIndex { mode } -> mode
    | BitHash { mode } -> mode
    | exception Not_found -> [] in
  let l = split_conj ~depth t in
  let clauses, program, lcs =
    List.fold_left (fun (clauses, programs, lcs) t ->       
      let clause, program, lcs = claux1 get_mode 0 depth [] [] 0 lcs t in
    clause :: clauses, program :: programs, lcs) ([],[],0) l in
  clauses, program, lcs
;;

let clausify1 ~loc m ~nargs ~depth t =
  claux1 ~loc (fun x -> try C.Map.find x m with Not_found -> [])
    nargs depth [] [] 0 0 t

end (* }}} *) 
open Clausify

(******************************************************************************
  Choice stack
 ******************************************************************************)

type goal = (*depth:*)int * prolog_prog * term

(* The activation frames points to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. For bad reasons, we call it lvl in the code. *)
type frame =
 | FNil
 | FCons of (*lvl:*)alternative * goal list * frame
and alternative = {
  lvl : alternative;
  program : prolog_prog;
  depth : int;
  goal : term;
  goals : goal list;
  stack : frame;
  trail : T.trail;
  state : state;
  clauses : clause list;
  next : alternative
}
let noalts : alternative = Obj.magic 0

(******************************************************************************
  Constraint propagation
 ******************************************************************************)

(* A runtime is a function to search for the first solution to the query
 * plus a function to find the next one.
 * The low level part of the runtime give access to the runtime memory.
 * One can for example execute code before starting the runtime and such
 * code may have effects "outside" the runtime that are trailed.  The destroy
 * function takes care of cleaning up the mess.
 *
 * The supported workflow is
 *   exec          optional, many times
 *   search        mandatory, 1 time
 *   next          optional, repeat until No_clause is thrown
 *   destroy       optional, 1 time, useful in nested runtimes
 *)

type 'x runtime = {
  search : unit -> alternative;
  next_solution : alternative -> alternative;

  (* low level part *)
  destroy : unit -> unit;
  exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  get : 'a. 'a Fork.local_ref -> 'a;
}

         
let do_make_runtime : (?max_steps:int -> ?delay_outside_fragment:bool -> 'x executable -> 'x runtime) ref =
 ref (fun ?max_steps ?delay_outside_fragment _ -> anomaly "do_make_runtime not initialized")

module Constraints : sig
    
  val propagation : unit -> constraint_def list
  val resumption : constraint_def list -> (int * prolog_prog * term) list

  val chrules : CHR.t Fork.local_ref

  (* out of place *)
  val exect_builtin_predicate :
    constant -> depth:int -> prolog_prog -> term list -> term list

end = struct (* {{{ *)

exception NoMatch

module Ice : sig
  
  type freezer

  val empty_freezer : freezer

  (* The input term lives in depth, the sequent lives in ground
   * (the same as depth for the goal, while >= for ctx items)
   *
   * shift = relocate only bound variables
   * relocate = increment all db indexes
   *
   * The input term is fully dereferenced, flexible terms are frozen,
   * it is shifted to its ground, then relocated to new base, then
   * shifted to the maxbase
   *)
  val freeze :
    depth:int -> term -> ground:int -> newground:int -> maxground:int ->
      freezer -> freezer * term

  val defrost :
    maxd:int -> term -> env -> to_:int -> freezer -> term

  val assignments : freezer -> assignment list

end = struct (* {{{ *)

  type freezer = {
    c2uv : uvar_body C.Map.t;
    uv2c : (uvar_body * term) list;
    assignments : assignment list; (* assignment to lower the level to 0 *)
  }

  let empty_freezer = { c2uv = C.Map.empty; uv2c = []; assignments = [] }

  let freeze ~depth t ~ground ~newground ~maxground f =
    let f = ref f in
    let log_assignment = function
      | t, None -> t
      | t, Some (r,_,nt as s) ->
          f := { !f with assignments = s :: !f.assignments };
          r @:= nt;
          t in
    let freeze_uv r =
      try List.assq r !f.uv2c
      with Not_found ->
        let n, c = C.fresh () in
        [%spy "freeze-add" (fun fmt tt ->
          Fmt.fprintf fmt "%s == %a" (C.show n) (ppterm 0 [] 0 empty_env) tt)
          (UVar (r,0,0))];
        f := { !f with c2uv = C.Map.add n r !f.c2uv;
                       uv2c = (r,c) :: !f.uv2c };
        c in
    let rec faux d = function
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) -> Cons(faux d hd, faux d tl)
      | App(c,x,xs) -> App(c,faux d x, List.map (faux d) xs)
      | Builtin(c,args) -> Builtin(c,List.map (faux d) args)
      | (Arg _ | AppArg _) -> error "only heap terms can be frozen"
      | Lam t -> Lam (faux (d+1) t)
      (* freeze *)
      | AppUVar(r,0,args) when !!r == C.dummy ->
          let args = List.map (faux d) args in
          App(C.uvarc, freeze_uv r, [list_to_lp_list args])
      (* expansion *)
      | UVar(r,lvl,ano) when !!r == C.dummy ->
          faux d (log_assignment(expand_uv ~depth:d r ~lvl ~ano))
      | AppUVar(r,lvl,args) when !!r == C.dummy ->
          faux d (log_assignment(expand_appuv ~depth:d r ~lvl ~args))
      (* deref *)
      | UVar(r,lvl,ano) -> faux d (deref_uv ~from:lvl ~to_:d ano !!r)
      | AppUVar(r,lvl,args) -> faux d (deref_appuv ~from:lvl ~to_:d args !!r)
    in
    [%spy "freeze-in" (fun fmt t ->
      Fmt.fprintf fmt "depth:%d ground:%d newground:%d maxground:%d %a"
        depth ground newground maxground (uppterm depth [] 0 empty_env) t) t];
    let t = faux depth t in
    [%spy "freeze-after-faux" (fun fmt t ->
      Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env) t) t];
    let t = shift_bound_vars ~depth ~to_:ground t in
    [%spy "freeze-after-shift->ground" (fun fmt t ->
      Fmt.fprintf fmt "%a" (uppterm ground [] 0 empty_env) t) t];
    let t = shift_bound_vars ~depth:0 ~to_:(newground-ground) t in
    [%spy "freeze-after-reloc->newground" (fun fmt t ->
      Fmt.fprintf fmt "%a" (uppterm newground [] 0 empty_env) t) t];
    let t = shift_bound_vars ~depth:newground ~to_:maxground t in
    [%spy "freeze-after-shift->maxground" (fun fmt t ->
      Fmt.fprintf fmt "%a" (uppterm maxground [] 0 empty_env) t) t];
    !f, t
       
  let defrost ~maxd t env ~to_ f =
  [%spy "defrost-in" (fun fmt t ->
    Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
      (uppterm maxd [] maxd env) t) t];
    let t = full_deref ~adepth:maxd env ~depth:maxd t in
  [%spy "defrost-fully-derefd" (fun fmt t ->
    Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
      (uppterm maxd [] 0 empty_env) t) t];
    let t = subtract_to_consts ~amount:(maxd - to_) ~depth:maxd t in
  [%spy "defrost-shifted" (fun fmt t ->
    Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
      (uppterm to_ [] 0 empty_env) t) t];
    let rec daux d = function
      | Const c when C.Map.mem c f.c2uv ->
          UVar(C.Map.find c f.c2uv,0,0)
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) -> Cons(daux d hd, daux d tl)
      | App(c,Const x,[args]) when c == C.uvarc ->
          let r = C.Map.find x f.c2uv in
          let args = lp_list_to_list ~depth:d args in
          mkAppUVar r 0 (List.map (daux d) args)
      | App(c,x,xs) -> App(c,daux d x, List.map (daux d) xs)
      | Builtin(c,args) -> Builtin(c,List.map (daux d) args)
      | Arg(i,ano) when env.(i) != C.dummy ->
          daux d (deref_uv ~from:to_ ~to_:d ano env.(i))
      | AppArg (i,args) when env.(i) != C.dummy ->
          daux d (deref_appuv ~from:to_ ~to_:d args env.(i))
      | (Arg(i,_) | AppArg(i,_)) as x ->
          env.(i) <- UVar(oref C.dummy, to_, 0);
          daux d x
      | Lam t -> Lam (daux (d+1) t)
      | UVar _ as x -> x
      | AppUVar(r,lvl,args) -> AppUVar(r,lvl,List.map (daux d) args)
    in
     daux to_ t

  let assignments { assignments } = assignments 

let replace_const m t =
  let rec rcaux = function
    | Const c as x -> (try mkConst (List.assoc c m) with Not_found -> x)
    | Lam t -> Lam (rcaux t)
    | App(c,x,xs) ->
        App((try List.assoc c m with Not_found -> c),
            rcaux x, smart_map rcaux xs)
    | Builtin(c,xs) -> Builtin(c,smart_map rcaux xs)
    | Cons(hd,tl) -> Cons(rcaux hd, rcaux tl)
    | (CData _ | UVar _ | Nil | Discard) as x -> x
    | Arg _ | AppArg _ -> assert false
    | AppUVar(r,lvl,args) -> AppUVar(r,lvl,smart_map rcaux args) in
  [%spy "alignment-replace-in" (uppterm 0 [] 0 empty_env)  t];
  let t = rcaux t in
  [%spy "alignment-replace-out" (uppterm 0 [] 0 empty_env) t];
  t
;;
let ppmap fmt (g,l) =
  let aux fmt (c1,c2) = Fmt.fprintf fmt "%s -> %s" (C.show c1) (C.show c2) in
  Fmt.fprintf fmt "%d = %a" g (pplist aux ",") l
;;


end (* }}} *)

let match_goal goalno maxground env freezer (newground,depth,t) pattern =
  let freezer, t =
    Ice.freeze ~depth t ~ground:depth ~newground ~maxground freezer in
  [%trace "matching" ("@[<hov>%a ===@ %a@]"
     (uppterm maxground [] maxground env) t
     (uppterm 0 [] maxground env) pattern) begin
  if unif ~matching:false maxground env 0 t pattern then freezer
  else raise NoMatch
  end]
  
let match_context goalno maxground env freezer (newground,ground,lt) pattern =
  let freezer, lt =
    map_acc (fun freezer { hdepth = depth; hsrc = t } ->
      Ice.freeze ~depth t ~ground ~newground ~maxground freezer)
    freezer lt in
  let t = list_to_lp_list lt in
  [%trace "matching" ("@[<hov>%a ===@ %a@]"
     (uppterm maxground [] maxground env) t
     (uppterm 0 [] maxground env) pattern) begin
  if unif ~matching:false maxground env 0 t pattern then freezer
  else raise NoMatch
  end]

(* To avoid matching the same propagation rule against the same ordered list
 * of constraints *)
type chrattempt = {
  propagation_rule : CHR.rule;
  constraints : constraint_def list
}
module HISTORY = Hashtbl.Make(struct
  type t = chrattempt
  let hash = Hashtbl.hash
  let equal { propagation_rule = p ; constraints = lp }
            { propagation_rule = p'; constraints = lp'} =
        p == p' && for_all2 (==) lp lp'
end)

let chrules = Fork.new_local CHR.empty

let delay_goal ?(filter_ctx=fun _ -> true) ~depth prog ~goal:g ~on:keys =
  let pdiff = local_prog prog in
  let pdiff = List.filter filter_ctx pdiff in
  [%spy "delay-goal" (fun fmt x-> Fmt.fprintf fmt
    (*"Delaying goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
    "@[<hov 2> ...@ ⊢^%d %a@]\n%!"
      (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*) depth
      (uppterm depth [] 0 empty_env) x) g];
  let kind = Constraint {
    cdepth = depth; prog = prog; context=pdiff; conclusion = g } in
  CS.declare_new { kind ; blockers = keys }
;;

let rec head_of = function
  | Const x -> x
  | App(x,Lam f,_) when C.(x == pic) -> head_of f
  | App(x,hd,_) when C.(x == rimplc) -> head_of hd
  | App(x,hd,_) when C.(x == andc) -> head_of hd (* FIXME *)
  | App(x,_,_) -> x
  | Builtin(x,_) -> x
  | AppUVar(r,_,_)
  | UVar(r,_,_) when !!r != C.dummy -> head_of !!r
  | CData _ -> type_error "A constraint cannot be a primitive data"
  | Cons(x,_) -> head_of x
  | Nil -> type_error "A constraint cannot be a list"
  | (UVar _ | AppUVar _) -> type_error "A constraint cannot have flexible head"
  | (Arg _ | AppArg _) -> anomaly "head_of on non-heap term"
  | Discard -> type_error "A constraint cannot be _"
  | Lam _ -> type_error "A constraint cannot be a function"

let dummy_uvar_body = { contents = C.dummy; rest = [] }

let declare_constraint ~depth prog args =
  let g, keys =
    match args with
    | [t1; t2] ->
      let err =
        "the second argument of declare_constraint must be a list of variables"
      in
      let rec collect_keys t = match deref_head ~depth t with
        | UVar (r, _, _) | AppUVar (r, _, _) -> [r]
        | Discard -> [dummy_uvar_body]
        | _ -> type_error err
      and collect_keys_list t = match deref_head ~depth t with
        | Nil -> []
        | Cons(hd,tl) -> collect_keys hd @ collect_keys_list tl
        | _ -> type_error err
      in
        t1, collect_keys_list t2
    | _ -> type_error "declare_constraint takes 2 arguments"
  in 
  match CHR.clique_of (head_of g) !chrules with
  | Some clique -> (* real constraint *)
     (* XXX head_of is weak because no clausify ? XXX *)
     delay_goal ~filter_ctx:(fun { hsrc = x } -> C.Set.mem (head_of x) clique)
       ~depth prog ~goal:g ~on:keys
  | None -> delay_goal ~depth prog ~goal:g ~on:keys

let type_err ~depth bname n ty t =
  type_error begin
    "builtin " ^ bname ^ ": " ^
    (if n = 0 then "" else string_of_int n ^ "th argument: ") ^
    "expected " ^ ty ^ ": got " ^
    match t with
    | None -> "_"
    | Some t -> Format.asprintf "%a" (uppterm depth [] 0 empty_env) t
  end

let wrap_type_err bname n f x =
  try f x
  with Conversion.TypeErr(ty,depth,t) -> type_err ~depth bname n (Conversion.show_ty_ast ty) (Some t)

let arity_err ~depth bname n t =
  type_error ("builtin " ^ bname ^ ": " ^ 
    match t with
    | None -> string_of_int n ^ "th argument is missing"
    | Some t -> "too many arguments at: " ^
                  Format.asprintf "%a" (uppterm depth [] 0 empty_env) t)

let out_of_term ~depth { Conversion.readback; ty } n bname hyps constraints state t =
  match deref_head ~depth t with
  | Discard -> BuiltInPredicate.Discard
  | _ -> BuiltInPredicate.Keep

let in_of_term ~depth { Conversion.readback } n bname hyps constraints state t =
  wrap_type_err bname n (readback ~depth hyps constraints state) t

let inout_of_term ~depth { Conversion.readback } n bname hyps constraints state t =
  match deref_head ~depth t with
  | Discard -> state, BuiltInPredicate.NoData
  | _ ->
     wrap_type_err bname n (fun () ->
       let state, t = readback ~depth hyps constraints state t in
       state, BuiltInPredicate.Data t) ()

let mk_out_assign ~depth { Conversion.embed } bname hyps constraints state input v  output =
  match output, input with
  | None, BuiltInPredicate.Discard -> state, []
  | Some _, BuiltInPredicate.Discard -> state, [] (* We could warn that such output was generated without being required *)
  | Some t, BuiltInPredicate.Keep ->
     let state, t, extra = embed ~depth hyps constraints state t in
     state, extra @ [App(C.eqc, v, [t])]
  | None, BuiltInPredicate.Keep ->
      anomaly ("ffi: " ^ bname ^ ": some output was requested but not produced")

let mk_inout_assign ~depth { Conversion.embed } bname hyps constraints state input v  output =
  match output, input with
  | None, BuiltInPredicate.NoData -> state, []
  | Some _, BuiltInPredicate.NoData -> state, [] (* We could warn that such output was generated without being required *)
  | Some t, BuiltInPredicate.Data _ ->
     let state, t, extra = embed ~depth hyps constraints state t in
     state, extra @ [App(C.eqc, v, [t])]
  | None, BuiltInPredicate.Data _ ->
      anomaly ("ffi: " ^ bname ^ ": some output was requested but not produced")

let call (BuiltInPredicate.Pred(bname,ffi,compute)) ~depth hyps constraints state data =
  let rec aux : type i o.
    (i,o) BuiltInPredicate.ffi -> compute:i -> reduce:(state -> o -> state * term list) ->
       term list -> int -> state -> state * term list =
  fun ffi ~compute ~reduce data n state ->
    match ffi, data with
    | BuiltInPredicate.Easy _, [] ->
       let result = wrap_type_err bname 0 (fun () -> compute ~depth) () in
       let state, l = reduce state result in
       state, List.rev l
    | BuiltInPredicate.Read _, [] ->
       let result = wrap_type_err bname 0 (compute ~depth hyps constraints) state in
       let state, l = reduce state result in
       state, List.rev l
    | BuiltInPredicate.Full _, [] ->
       let state, result, gls = wrap_type_err bname 0 (compute ~depth hyps constraints) state in
       let state, l = reduce state result in
       state, gls @ List.rev l
    | BuiltInPredicate.VariadicIn(d, _), data ->
       let state, i =
         map_acc (in_of_term ~depth d n bname hyps constraints) state data in
       let state, rest = wrap_type_err bname 0 (compute i ~depth hyps constraints) state in
       let state, l = reduce state rest in
       state, List.rev l
    | BuiltInPredicate.VariadicOut(d, _), data ->
       let i = List.map (out_of_term ~depth d n bname hyps constraints state) data in
       let state, (rest, out) = wrap_type_err bname 0 (compute i ~depth hyps constraints) state in
       let state, l = reduce state rest in
       begin match out with
         | Some out ->
             let state, ass =
               map_acc3 (mk_out_assign ~depth d bname hyps constraints) state i data out in 
             state, List.(rev (concat ass @ l))
         | None -> state, List.rev l
       end
    | BuiltInPredicate.VariadicInOut(d, _), data ->
       let state, i =
         map_acc (inout_of_term ~depth d n bname hyps constraints) state data in
       let state, (rest, out) = wrap_type_err bname 0 (compute i ~depth hyps constraints) state in
       let state, l = reduce state rest in
       begin match out with
         | Some out ->
             let state, ass =
               map_acc3 (mk_inout_assign ~depth d bname hyps constraints) state i data out in 
             state, List.(rev (concat ass @ l))
         | None -> state, List.rev l
       end
    | BuiltInPredicate.In(d, _, ffi), t :: rest ->
        let state, i = in_of_term ~depth d n bname hyps constraints state t in
        aux ffi ~compute:(compute i) ~reduce rest (n + 1) state
    | BuiltInPredicate.Out(d, _, ffi), t :: rest ->
        let i = out_of_term ~depth d n bname hyps constraints state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_out_assign ~depth d bname hyps constraints state i t out in
          state, ass @ l in
        aux ffi ~compute:(compute i) ~reduce rest (n + 1) state
    | BuiltInPredicate.InOut(d, _, ffi), t :: rest ->
        let state, i = inout_of_term ~depth d n bname hyps constraints state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_inout_assign ~depth d bname hyps constraints state i t out in
          state, ass @ l in
        aux ffi ~compute:(compute i) ~reduce rest (n + 1) state

    | _, t :: _ -> arity_err ~depth bname n (Some t)
    | _, [] -> arity_err ~depth bname n None

  in
    let reduce state _ = state, [] in
    aux ffi ~compute ~reduce data 1 state
;;

let exect_builtin_predicate c ~depth idx args =
       if c == C.declare_constraintc then begin
               declare_constraint ~depth idx args; [] end
  else if c == C.print_constraintsc then begin
               printf "@[<hov 0>%a@]%!" CS.print (CS.contents ());
               [] 
  end else
    let b =
      try BuiltInPredicate.lookup c
      with Not_found -> 
        anomaly ("no built-in predicated named " ^ C.show c) in
    let constraints = !CS.Ugly.delayed in
    let state = !CS.state  in
    let state, gs = call b ~depth (local_prog idx) constraints state args in
    CS.state := state;
    gs
;;

let match_head { conclusion = x; cdepth } p =
  match deref_head ~depth:cdepth x with
  | Const x -> x == p
  | App(x,_,_) -> x == p
  | _ -> false
;;

let try_fire_rule rule (constraints as orig_constraints) =

  let { CHR.
    to_match = pats_to_match;
    to_remove = pats_to_remove;
    patsno;
    new_goal; guard; nargs;
    pattern = quick_filter;
    rule_name } = rule in

  if patsno < 1 then
    error "CHR propagation must mention at least one constraint";

  (* Quick filtering using just the head symbol *)
  if not(List.for_all2 match_head constraints quick_filter) then None else

    (* max depth of rule and constraints involved in the matching *)
  let max_depth, constraints =
    (* Goals are lifted at different depths to avoid collisions *)
    let max_depth,constraints = 
     List.fold_left (fun (md,res) c ->
        let md = md + c.cdepth in
        md, (md,c)::res)
       (0,[]) constraints in
    max_depth, List.rev constraints
  in
 
  let constraints_depts, constraints_contexts, constraints_goals =
    List.fold_right
      (fun (dto,{context = c; cdepth = d; conclusion = g}) 
           (ds, ctxs, gs) ->
        (dto,d,d) :: ds, (dto,d,c) :: ctxs, (dto,d,g) :: gs)
      constraints ([],[],[]) in
 
  let env = Array.make nargs C.dummy in
 
  let patterns_eigens, patterns_contexts, patterns_goals =
    List.fold_right (fun { CHR.eigen; context; conclusion } (es, cs, gs) ->
      eigen :: es, context :: cs, conclusion :: gs)
    (pats_to_match @ pats_to_remove) ([],[],[]) in
  
  let match_eigen i m (dto,d,eigen) pat =
    match_goal i max_depth env m (dto,d,Data.C.of_int eigen) pat in
  let match_conclusion i m g pat =
    match_goal i max_depth env m g pat in
  let match_context i m ctx pctx =
    match_context i max_depth env m ctx pctx in
 
  let guard =
    match guard with
    | Some g -> g
    | None -> Constants.truec
  in
 
  let initial_program = !orig_prolog_program in
 
  let executable = {
    (* same program *)
    compiled_program = initial_program; 
    (* no meta meta level *)
    chr = CHR.empty;
    initial_goal =
      move ~adepth:max_depth ~from:max_depth ~to_:max_depth env
        (shift_bound_vars ~depth:0 ~to_:max_depth guard);
    assignments = StrMap.empty;
    initial_depth = max_depth;
    initial_state = State.(init () |> end_compilation StrMap.empty);
    query_arguments = Query.N;
  } in
  let { search; get; exec; destroy } = !do_make_runtime executable in
 
  let check_guard () =
    try
      let _ = search () in
      if get CS.Ugly.delayed <> [] then
        error "propagation rules must declare constraint(s)"
    with No_clause -> raise NoMatch in
 
  let result = try

    (* matching *)
    let m = exec (fun m ->      
      [%spy "propagate-try-on"
        (pplist (fun f (dto,dt,t) ->
           Format.fprintf f "(lives-at:%d, to-be-lifted-to:%d) %a"
             dt dto (uppterm dt [] 0 empty_env) t) ";") 
           constraints_goals];

      let m = fold_left2i match_eigen m
        constraints_depts patterns_eigens in
      let m = fold_left2i match_conclusion m
        constraints_goals patterns_goals in
      let m = fold_left2i match_context m
        constraints_contexts patterns_contexts in

      [%spy "propagate-matched-args"
        (pplist (uppterm max_depth [] 0 empty_env) ~boxed:false ",")
        (Array.to_list env)];

      T.to_resume := [];
      assert(!T.new_delayed = []);
      m) Ice.empty_freezer in

    [%spy "propagate-try-rule-guard" (fun fmt () -> Format.fprintf fmt 
        "@[<hov 2>depth=%d@ @]" max_depth) ()];

    check_guard ();

    (* result *)
    let _, constraints_to_remove =
      let len_pats_to_match = List.length pats_to_match in
      partition_i (fun i _ -> i < len_pats_to_match) orig_constraints in
    let new_goals =
      match new_goal with
      | None -> []
      | Some { CHR.eigen; context; conclusion } ->
      let eigen =
        match full_deref ~adepth:max_depth env ~depth:max_depth eigen with
        | CData x when Data.C.is_int x -> Data.C.to_int x
        | Discard -> max_depth
        | _ -> error "eigen not resolving to an integer" in
      let conclusion =
        Ice.defrost ~maxd:max_depth ~to_:eigen
          (App(C.implc,context,[conclusion])) env m in
      (* TODO: check things make sense in heigen *)
      let prog = initial_program in
      [{ cdepth = eigen; prog; context = []; conclusion }] in
    [%spy "propagate-delivery" Fmt.pp_print_string "delivered"];
    Some(rule_name, constraints_to_remove, new_goals, Ice.assignments m)
  with NoMatch ->
    [%spy "propagate-try-rule-fail" (fun _ _ -> ()) ()];
    None
  in
  destroy ();
  result
;;

let resumption to_be_resumed_rev =
  List.map (fun { cdepth = d; prog; conclusion = g } ->
    [%spy "run-scheduling-resume"
      (fun fmt -> Fmt.fprintf fmt "%a" (uppterm d [] d empty_env)) g];
    d, prog, g)
  (List.rev to_be_resumed_rev)

(* all permutations of pivot+rest of length len where the
 * pivot is in pivot_position. pivot may be part of rest, it is automatically
 * ignored  *)
let mk_permutations len pivot pivot_position rest =
  let open List in
  let rec insert x = function
    | [] -> [[x]]
    | (hd::tl) as l -> (x::l) :: map (fun y -> hd :: y) (insert x tl) in
  let rec aux n l =
    if n = 0 then [[]] else
    match l with 
    | [] -> []
    | hd :: tl when hd == pivot -> aux n tl
    | hd :: tl-> flatten (map (insert hd) (aux (n-1) tl)) @ aux n tl in

  let permutations_no_pivot = aux (len - 1) rest in
  
  permutations_no_pivot |> map begin fun l ->
    let before, after = partition_i (fun i _ -> i < pivot_position) l in
    before @ pivot :: after
  end
;;

let propagation () =
  let to_be_resumed_rev = ref [] in
  let removed = ref [] in
  let outdated cs = List.exists (fun x -> List.memq x !removed) cs in
  while !CS.new_delayed <> [] do
    match !CS.new_delayed with
    | [] -> anomaly "Empty list"
    | { CS.cstr = active; cstr_blockers = overlapping } :: rest ->

       (* new_delayed may be changed by, CS.remove_old_constraint *)
       CS.new_delayed := rest;

       let rules = CHR.rules_for (head_of active.conclusion) !chrules in

       rules |> List.iter (fun rule ->

         for position = 0 to rule.CHR.patsno - 1 do

           (* don't generate perms if the pivot is already out of place *)
           if not (match_head active (List.nth rule.CHR.pattern position))
           then ()
           else

           let permutations = 
             mk_permutations rule.CHR.patsno active position
               (List.map fst (CS.contents ~overlapping ())) in

           permutations |> List.iter (fun constraints ->

             (* a constraint just removed may occur in a permutation (that
              * was generated before the removal *)
             if outdated constraints then ()
             else
               match try_fire_rule rule constraints with
               | None -> ()
               | Some (rule_name, to_be_removed, to_be_added, assignments) ->
                   [%spy "run-CHR-rule-fired" Fmt.pp_print_string rule_name];
                   removed := to_be_removed @ !removed;
                   List.iter CS.remove_old_constraint to_be_removed;
                   List.iter (fun (r,_lvl,t) -> r @:= t) assignments;
                   to_be_resumed_rev := to_be_added @ !to_be_resumed_rev)
         done);
  done;
  !to_be_resumed_rev

end (* }}} *)

(******************************************************************************
  Main loop = SLD + delay/resumption
 ******************************************************************************)

module Mainloop : sig

  val make_runtime : ?max_steps:int -> ?delay_outside_fragment:bool -> 'x executable -> 'x runtime

end = struct (* {{{ *)

let steps_bound = Fork.new_local None
let steps_made = Fork.new_local 0

let pred_of g =
  match g with
  | App(c,_,_) -> Some(C.show c)
  | Const c -> Some(C.show c)
  | Builtin(c,_) -> Some(C.show c)
  | _ -> None

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ?max_steps: int -> ?delay_outside_fragment: bool -> 'x executable -> 'x runtime =
  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     depth >= 0 is the number of variables in the context. *)
  let rec run depth p g gs (next : frame) alts lvl =
    [%cur_pred (pred_of g)];
    [%trace "run" (fun _ -> ()) begin

    begin match !steps_bound with
    | Some bound ->
        incr steps_made; if !steps_made > bound then raise No_more_steps
    | None -> ()
    end;

 match resume_all () with
 | None ->
     [%spy "run-resumed-fail" (fun _ _ -> ()) ()];
     [%tcall next_alt alts]
 | Some ((ndepth,np,ng)::goals) ->
    [%spy "run-resumed-goal" (fun fmt -> Fmt.fprintf fmt "%a" (ppterm ndepth [] 0 empty_env)) ng];
    [%tcall run ndepth np ng (goals@(depth,p,g)::gs) next alts lvl]
 | Some [] ->
    [%spy "run-goal" (fun fmt -> Fmt.fprintf fmt "%a" (uppterm depth [] 0 empty_env)) g];
    match g with
    | Builtin(c,[]) when c == C.cutc -> [%tcall cut p gs next alts lvl]
    | App(c, g, gs') when c == C.andc || c == C.andc2 ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    | Cons (g,gs') ->
       run depth p g ((depth,p,gs') :: gs) next alts lvl
    | Nil -> 
      begin match gs with
      | [] -> pop_andl alts next lvl
      | (depth, p, g) :: gs -> run depth p g gs next alts lvl end
    | App(c, g2, [g1]) when c == C.rimplc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, pdiff, lcs = clausify p ~depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses ~depth clauses pdiff p) g2 gs next alts lvl
    | App(c, g1, [g2]) when c == C.implc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, pdiff, lcs = clausify p ~depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses ~depth clauses pdiff p) g2 gs next alts lvl
(*  This stays commented out because it slows down rev18 in a visible way!   *)
(*  | App(c, _, _) when c == implc -> anomaly "Implication must have 2 args" *)
    | App(c, arg, []) when c == C.pic ->
       let f = get_lambda_body ~depth arg in
       run (depth+1) p f gs next alts lvl
    | App(c, arg, []) when c == C.sigmac ->
       let f = get_lambda_body ~depth arg in
       let v = UVar(oref C.dummy, depth, 0) in
       run depth p (subst depth [v] f) gs next alts lvl
    | UVar ({ contents = g }, from, args) when g != C.dummy ->
       run depth p (deref_uv ~from ~to_:depth args g) gs next alts lvl
    | AppUVar ({contents = t}, from, args) when t != C.dummy ->
       run depth p (deref_appuv ~from ~to_:depth args t) gs next alts lvl 
    | Const _ | App _ -> (* Atom case *)
       let cp = get_clauses depth g p in
       [%tcall backchain depth p g gs cp next alts lvl]
    | Arg _ | AppArg _ -> anomaly "Not a heap term"
    | Lam _ | CData _ ->
        type_error ("The goal is not a predicate:" ^ (show_term g))
    | UVar _ | AppUVar _ | Discard ->
        error "The goal is a flexible term"
    | Builtin(c, args) ->
       match Constraints.exect_builtin_predicate c ~depth p args with
       | gs' ->
          (match List.map (fun g -> depth,p,g) gs' @ gs with
           | [] -> [%tcall pop_andl alts next lvl]
           | (depth,p,g) :: gs -> run depth p g gs next alts lvl)
       | exception No_clause -> [%tcall next_alt alts]
  end]

  and backchain depth p g gs cp next alts lvl =
    let maybe_last_call = alts == noalts in
    let rec args_of = function
      | Const k -> k, []
      | App(k,x,xs) -> k, x::xs
      | UVar ({ contents = g },origdepth,args) when g != C.dummy ->
         args_of (deref_uv ~from:origdepth ~to_:depth args g) 
      | AppUVar({ contents = g },origdepth,args) when g != C.dummy ->
         args_of (deref_appuv ~from:origdepth ~to_:depth args g) 
      | _ -> anomaly "ill-formed goal" in
    let k, args_of_g = args_of g in
    let rec select l =
      [%trace "select" (fun fmt ->
          pplist ~max:1 ~boxed:true (fun fmt -> ppclause fmt ~depth k) "|" fmt l)
      begin match l with
      | [] -> [%tcall next_alt alts]
      | c :: cs ->
        let old_trail = !T.trail in
        T.last_call := maybe_last_call && cs = [];
        let env = Array.make c.vars C.dummy in
        match
         for_all3b (fun x y matching -> unif ~matching depth env c.depth x y)
           args_of_g c.args c.mode false
        with
        | false -> T.undo old_trail (); [%tcall select cs]
        | true ->
           let oldalts = alts in
           let alts = if cs = [] then alts else
             { program = p; depth = depth; goal = g; goals = gs; stack = next;
               trail = old_trail;
               state = !CS.state;
               clauses = cs; lvl = lvl ; next = alts} in
           begin match c.hyps with
           | [] ->
              begin match gs with
              | [] -> [%tcall pop_andl alts next lvl]
              | (depth,p,g)::gs -> [%tcall run depth p g gs next alts lvl] end
           | h::hs ->
              let next = if gs = [] then next else FCons (lvl,gs,next) in
              let h = move ~adepth:depth ~from:c.depth ~to_:depth env h in
              let hs =
                List.map (fun x->
                  depth,p,move ~adepth:depth ~from:c.depth ~to_:depth env x)
                hs in
              [%tcall run depth p h hs next alts oldalts] end
      end] in
      select cp

  and cut p gs next alts lvl =
    (* cut the or list until the last frame not to be cut (called lvl) *)
    let rec prune alts = if alts == lvl then alts else prune alts.next in
    let alts = prune alts in
    (* XXX what about custom constraints *)
    if alts == noalts then T.cut_trail ();
    match gs with
    | [] -> pop_andl alts next lvl
    | (depth, p, g) :: gs -> run depth p g gs next alts lvl

  and pop_andl alts next lvl =
   match next with
    | FNil ->
        (match resume_all () with
           None ->
            Fmt.fprintf Fmt.std_formatter
             "Undo triggered by goal resumption\n%!";
            [%tcall next_alt alts]
         | Some ((ndepth,p,ng)::goals) ->
            run ndepth p ng goals FNil alts lvl
         | Some [] -> alts)
    | FCons (_,[],_) -> anomaly "empty stack frame"
    | FCons(lvl,(depth,p,g)::gs,next) ->
        run depth p g gs next alts lvl

  and resume_all () =
(*     if fm then Some [] else *)
(*if (!to_resume <> []) then begin
prerr_endline ("## RESUME ALL R " ^ string_of_int (List.length !to_resume));
prerr_endline ("## RESUME ALL D " ^ string_of_int (List.length !delayed));
end;*)
   let ok = ref true in
   let to_be_resumed = ref [] in
   (* Phase 1: we analyze the goals to be resumed *)
   while !ok && !CS.to_resume <> [] do
     match !CS.to_resume with
     | { kind = Unification { adepth; bdepth; env; a; b; matching } } as dg :: rest ->
         CS.remove_old dg;
         CS.to_resume := rest;
         [%spy "run-resumed-unif" (fun fmt _ -> Fmt.fprintf fmt 
           "@[<hov 2>^%d:%a@ == ^%d:%a@]\n%!"
           adepth (uppterm adepth [] 0 empty_env) a
           bdepth (uppterm bdepth [] adepth env) b) ()];
         ok := unif ~matching adepth env bdepth a b
     | { kind = Constraint dpg } as c :: rest ->
         CS.remove_old c;
         CS.to_resume := rest;
         (*Fmt.fprintf Fmt.std_formatter
          "Resuming goal: @[<hov 2> ...@ ⊢^%d %a@]\n%!"
          (*"Resuming goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
          (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*)
          depth (uppterm depth [] 0 empty_env) g ;*)
         to_be_resumed := dpg :: !to_be_resumed
     | _ -> anomaly "Unknown constraint type"
   done ;
   (* Phase 2: we propagate the constraints *)
   if !ok then
     (* Optimization: check here new_delayed *)
     if !CS.new_delayed <> [] then Some (Constraints.resumption (Constraints.propagation () @ !to_be_resumed))
     else Some (Constraints.resumption !to_be_resumed)
   else None

  and next_alt alts =
   if alts == noalts then raise No_clause
   else
     let { program = p; clauses; goal = g; goals = gs; stack = next;
          trail = old_trail; state = old_state;
          depth = depth; lvl = lvl; next = alts} = alts in
    T.undo ~old_trail ~old_state ();
    backchain depth p g gs clauses next alts lvl (* XXX *)
  in


 (* Finally the runtime *)
 fun ?max_steps ?(delay_outside_fragment = false) {
    compiled_program;
    chr;
    initial_depth;
    initial_goal;
    initial_state;
    assignments;
  } ->
  let { Fork.exec = exec ; get = get ; set = set } = Fork.fork () in
  set orig_prolog_program compiled_program;
  set Constraints.chrules chr;
  set T.initial_trail T.empty;
  set T.trail T.empty;
  set T.last_call false;
  set CS.new_delayed [];
  set CS.to_resume [];
  set CS.Ugly.delayed [];
  set steps_bound max_steps;
  set delay_hard_unif_problems delay_outside_fragment;
  set steps_made 0;
  set CS.state initial_state;
  let search = exec (fun () ->
     [%spy "run-trail" (fun fmt _ -> T.print_trail fmt) ()];
     T.initial_trail := !T.trail;
     run initial_depth !orig_prolog_program initial_goal [] FNil noalts noalts) in
  let destroy () = exec (fun () -> T.undo ~old_trail:T.empty ()) () in
  let next_solution = exec next_alt in
  { search; next_solution; destroy; exec; get }
;;

do_make_runtime := make_runtime;;

end (* }}} *)
open Mainloop

(******************************************************************************
  API
 ******************************************************************************)

let mk_outcome search get_cs assignments =
 try
   let alts = search () in
   let syn_csts, state, qargs = get_cs () in
   let solution = {
     assignments;
     constraints = syn_csts;
     state;
     output = Query.output qargs assignments state syn_csts;
   } in
   Success solution, alts
 with
 | No_clause (*| Non_linear*) -> Failure, noalts
 | No_more_steps -> NoMoreSteps, noalts

let execute_once ?max_steps ?delay_outside_fragment exec =
 auxsg := [];
 let { search; get } = make_runtime ?max_steps ?delay_outside_fragment exec in
 fst (mk_outcome search (fun () -> get CS.Ugly.delayed, get CS.state, exec.query_arguments) exec.assignments)
;;

let execute_loop ?delay_outside_fragment exec ~more ~pp =
 let { search; next_solution; get } = make_runtime ?delay_outside_fragment exec in
 let k = ref noalts in
 let do_with_infos f =
  let time0 = Unix.gettimeofday() in
  let o, alts = mk_outcome f (fun () -> get CS.Ugly.delayed, get CS.state, exec.query_arguments) exec.assignments in
  let time1 = Unix.gettimeofday() in
  k := alts;
  pp (time1 -. time0) o in
 do_with_infos search;
 while !k != noalts do
   if not(more()) then k := noalts else
   try do_with_infos (fun () -> next_solution !k)
   with No_clause -> pp 0.0 Failure; k := noalts
 done
;;

let print_constraints () = CS.print Fmt.std_formatter (CS.contents ())
let pp_stuck_goal fmt s = CS.pp_stuck_goal fmt s
let is_flex = HO.is_flex
let deref_uv = HO.deref_uv
let deref_appuv = HO.deref_appuv
let deref_head = HO.deref_head
let make_runtime = Mainloop.make_runtime
let lp_list_to_list = Clausify.lp_list_to_list
let list_to_lp_list = HO.list_to_lp_list
let split_conj = Clausify.split_conj
let mkAppArg = HO.mkAppArg
let subst ~depth = HO.subst depth
let move = HO.move
let hmove = HO.hmove
let make_index = make_index
let clausify1 = Clausify.clausify1

(* vim: set foldmethod=marker: *)
