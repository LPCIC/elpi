(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser

module Fmt = Format
module F = Ast.Func
open Util
open Data

(* Internal notion of constraint *)
type constraint_def = {
  cdepth : int;
  prog : prolog_prog [@equal fun _ _ -> true]
               [@printer (fun fmt _ -> Fmt.fprintf fmt "<prolog_prog>")];
  context : clause_src list;
  conclusion : term;
  cgid : UUID.t [@trace];
}
type 'unification_def stuck_goal_kind +=
 | Constraint of constraint_def
let get_suspended_goal = function
  | Constraint { cdepth; conclusion; context; _ } -> Some { context ; goal = (cdepth, conclusion) }
  | _ -> None

(* Constants *)
module C : sig

  type t = Constants.t

  module Map = Constants.Map
  module Set = Constants.Set

  val show : ?table:symbol_table -> t -> string
  val pp : ?table:symbol_table -> Fmt.formatter -> t -> unit

  val mkConst : constant -> term
  val mkAppL : constant -> term list -> term

  val fresh_global_constant : unit -> constant * term

  (* mkinterval d n 0 = [d; ...; d+n-1] *)
  val mkinterval : int -> int -> int -> term list
  val dummy : term

  val table : symbol_table Fork.local_ref

end = struct

  type t = Constants.t
  let dummy = Data.dummy

let table = Fork.new_local {
  c2s = Constants.Map.empty;
  c2t = Hashtbl.create 37;
  frozen_constants = 0;
}

(* let () = at_exit (fun () -> let open Hashtbl in let s = stats !table.c2t in
  Array.iter (fun i -> Printf.eprintf "%d\n" i) s.bucket_histogram) *)

let show ?(table = !table) n =
  try Constants.Map.find n Global_symbols.table.c2s
  with Not_found ->
    try Constants.Map.find n table.c2s
    with Not_found ->
      if n >= 0 then "c" ^ string_of_int n
      else "SYMBOL" ^ string_of_int n

let pp ?table fmt n =
  Format.fprintf fmt "%s" (show ?table n)

let mkConst x =
  try Hashtbl.find !table.c2t x
  with Not_found ->
    let xx = Const x in
    Hashtbl.add !table.c2t x xx;
    xx
  [@@inline]
  
let fresh_global_constant () =
   !table.frozen_constants <- !table.frozen_constants - 1;
   let n = !table.frozen_constants in
   let xx = Const n in
   !table.c2s <- Constants.Map.add n ("frozen-" ^ string_of_int n) !table.c2s ;
   Hashtbl.add !table.c2t n xx;
   n, xx

module Map = Constants.Map
module Set = Constants.Set

(* - negative constants are global names
   - constants are hashconsed (terms)
   - we use special constants to represent !, pi, sigma *)

(* mkinterval d n 0 = [d; ...; d+n-1] *)
let rec mkinterval depth argsno n =
 if n = argsno then []
 else mkConst (n+depth)::mkinterval depth argsno (n+1)
;;

let mkAppL c = function
  | [] -> mkConst c
  | x::xs -> mkApp c x xs [@@inline]

end
let mkConst = C.mkConst

(* Dereferencing an UVar(r,args) when !!r != dummy requires a function
   of this kind.  The pretty printer needs one but will only be defined
   later, since we need, for example, beta reduction to implement it *)
type 'args deref_fun =
  ?avoid:uvar_body -> from:int -> to_:int -> 'args -> term -> term

module Pp : sig

  (* Low level printing *)
  val ppterm : ?pp_ctx:pp_ctx -> ?min_prec:int ->
    (*depth:*)int -> (*names:*)string list -> argsdepth:int -> env ->
    Fmt.formatter -> term -> unit

  (* For user consumption *)
  val uppterm : ?pp_ctx:pp_ctx -> ?min_prec:int ->
    (*depth:*)int -> (*names:*)string list -> argsdepth:int -> env ->
    Fmt.formatter -> term -> unit

  (* To be assigned later, used to dereference an UVar/AppUVar *)
  val do_deref : int deref_fun ref
  val do_app_deref : term list deref_fun ref

  (* To put it in the solution *)
  val uv_names : (string IntMap.t * int) Fork.local_ref

  val pp_oref : ?pp_ctx:pp_ctx -> Format.formatter -> (Util.UUID.t * Obj.t) -> unit

  val pp_constant : ?pp_ctx:pp_ctx -> Format.formatter -> constant -> unit

end = struct (* {{{ *)

let do_deref = ref (fun ?avoid ~from ~to_ _ _ -> assert false);;
let do_app_deref = ref (fun ?avoid ~from ~to_ _ _ -> assert false);;

let uv_names = Fork.new_local (IntMap.empty, 0)

let min_prec = Elpi_parser.Parser_config.min_precedence
let appl_prec = Elpi_parser.Parser_config.appl_precedence
let lam_prec = Elpi_parser.Parser_config.lam_precedence
let inf_prec = Elpi_parser.Parser_config.inf_precedence

let xppterm ~nice ?(pp_ctx = { Data.uv_names; table = ! C.table }) ?(min_prec=min_prec) depth0 names ~argsdepth env f t =
  let pp_app f pphd pparg ?pplastarg (hd,args) =
   if args = [] then pphd f hd
   else
    Fmt.fprintf f "@[<hov 1>%a@ %a@]" pphd hd
     (pplist pparg ?pplastelem:pplastarg " ") args in
  let ppconstant f c = Fmt.fprintf f "%s" (C.show ~table:pp_ctx.table c) in
  let rec pp_uvar prec depth vardepth args f r =
   if !!r == C.dummy then begin
    let s =
     try IntMap.find (uvar_id r) (fst !(pp_ctx.uv_names))
     with Not_found ->
      let m, n = !(pp_ctx.uv_names) in
      let s = "X" ^ string_of_int n in
      let n = n + 1 in
      let m = IntMap.add (uvar_id r) s m in
      pp_ctx.uv_names := (m,n);
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
      pplist ~boxed:true (aux Elpi_parser.Parser_config.comma_precedence depth) ", " f prefix ;
      if last != Nil then begin
       Fmt.fprintf f " | " ;
       aux prec 1 f last
      end;
      Fmt.fprintf f "]"
    | Const s -> ppconstant f s
    | App (hd,x,xs) ->
       (try
         let prec, hdlvl =
           Elpi_parser.Parser_config.precedence_of (C.show ~table:pp_ctx.table hd) in
         with_parens hdlvl
         (fun _ ->
          let open Elpi_lexer_config.Lexer_config in
          match prec with
          | Some Infix when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Some Infixl when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux hdlvl depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Some Infixr when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux hdlvl depth) (List.hd xs)
          | Some Prefix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" ppconstant hd
              (aux hdlvl depth) x
          | Some Postfix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" (aux hdlvl depth) x
              ppconstant hd 
          | _ ->
             pp_app f ppconstant (aux inf_prec depth)
              ~pplastarg:(aux_last inf_prec depth) (hd,x::xs))
        with Not_found -> 
         let lastarg = List.nth (x::xs) (List.length xs) in
         let hdlvl =
          if is_lambda depth lastarg then lam_prec
          else if hd == Global_symbols.andc then 110
          else appl_prec in
         with_parens hdlvl (fun _ ->
          if hd == Global_symbols.andc then
            pplist (aux inf_prec depth) ~pplastelem:(aux_last inf_prec depth) ", " f (x::xs)
          else pp_app f ppconstant (aux inf_prec depth)
                 ~pplastarg:(aux_last inf_prec depth) (hd,x::xs)))
    | Builtin (hd,[a;b]) when hd == Global_symbols.eqc ->
       let _, hdlvl =
         Elpi_parser.Parser_config.precedence_of (C.show ~table:pp_ctx.table hd) in
       with_parens hdlvl (fun _ ->
         Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
           (aux (hdlvl+1) depth) a ppconstant hd
           (aux (hdlvl+1) depth) b)
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

let pp_oref ?pp_ctx fmt (id,t) =
  if not (UUID.equal id id_term) then anomaly "pp_oref"
  else
    let t : term = Obj.obj t in
    if t == C.dummy then Fmt.fprintf fmt "_"
    else uppterm ?pp_ctx 0  [] ~argsdepth:0 empty_env fmt t

let pp_constant ?pp_ctx fmt c =
  let table =
    match pp_ctx with
    | None -> None
    | Some { table } -> Some table in
  C.pp ?table fmt c

end (* }}} *)

open Pp

let rid, max_runtime_id = Fork.new_local 0, ref 0

(******************************************************************************
  Stores for:
   - backtracking (trail)
   - constraints (delayed goals)
   - constraint handling rules (propagation rules)
  Note: propagation code for CHR rules is later
 ******************************************************************************)

(* Together to hide low level APIs of ConstraintStore needed by Trail *)
module ConstraintStoreAndTrail : sig

  type propagation_item = {
     cstr : constraint_def;
     cstr_blockers : uvar_body list;
  }

  val new_delayed      : propagation_item list Fork.local_ref
  val to_resume        : stuck_goal list Fork.local_ref

  val blockers_map     : stuck_goal list IntMap.t Fork.local_ref
  val blocked_by       : uvar_body -> stuck_goal list

  val declare_new : stuck_goal -> unit
  val remove_old : stuck_goal -> unit
  val remove_old_constraint : constraint_def -> unit

  val contents :
    ?overlapping:uvar_body list -> unit -> (constraint_def * blockers) list
  val print : ?pp_ctx:pp_ctx -> Fmt.formatter -> (constraint_def * blockers) list -> unit
  val print1 : ?pp_ctx:pp_ctx -> Fmt.formatter -> constraint_def * blockers -> unit
  val print_gid: Fmt.formatter -> constraint_def * blockers -> unit
  val pp_stuck_goal : ?pp_ctx:pp_ctx -> Fmt.formatter -> stuck_goal -> unit

  val state : State.t Fork.local_ref
  val initial_state : State.t Fork.local_ref

  (* ---------------------------------------------------- *)

  type trail
 
  val empty : trail

  val initial_trail : trail Fork.local_ref
  val trail : trail Fork.local_ref
  val cut_trail : unit -> unit 

  (* If true, no need to trail an imperative action.  Not part of trial_this
   * because you can save allocations and a function call by testing locally *)
  val last_call : bool ref

  (* add an item to the trail *)
  val trail_assignment : uvar_body -> unit           
  val trail_stuck_goal_addition : stuck_goal -> unit 
  val trail_stuck_goal_removal : stuck_goal -> unit  

  (* backtrack *)
  val undo :
    old_trail:trail -> ?old_state:State.t -> unit -> unit

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
    Fork.new_local State.dummy
  let initial_state =
    Fork.new_local State.dummy

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

let cut_trail () = trail := !initial_trail [@@inline];;
let blockers_map = Fork.new_local (IntMap.empty : stuck_goal list IntMap.t)
let blocked_by r = IntMap.find (uvar_id r) !blockers_map

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
  [%spy "dev:trail:assign" ~rid Fmt.pp_print_bool !last_call pp_trail_item (Assignement x)];
  if not !last_call then trail := Assignement x :: !trail
  [@@inline]
;;
let trail_stuck_goal_addition x =
  [%spy "dev:trail:add-constraint" ~rid Fmt.pp_print_bool !last_call pp_trail_item (StuckGoalAddition x)];
  if not !last_call then trail := StuckGoalAddition x :: !trail
  [@@inline]
;;
let trail_stuck_goal_removal x =
  [%spy "dev:trail:remove-constraint" ~rid Fmt.pp_print_bool !last_call pp_trail_item (StuckGoalRemoval x)];
  if not !last_call then trail := StuckGoalRemoval x :: !trail
  [@@inline]
;;

let append_blocked blocked map r =
  let blocker = uvar_id r in
  try
    let old = IntMap.find blocker map in
    (*assert(b.uid <= 0);*)
    IntMap.add blocker (blocked :: old) map
  with Not_found ->
    uvar_set_blocker r;
    IntMap.add blocker (blocked :: []) map

let remove_blocked blocked map r =
  let blocker = uvar_id r in
  (*try*)
    let old = IntMap.find blocker map in
    (*assert(b.uid <= 0);*)
    let l = remove_from_list blocked old in
    if l = [] then begin
      uvar_unset_blocker r;
      IntMap.remove blocker map
    end else
      IntMap.add blocker l map
  (*with Not_found ->
    assert(b.uid >= 0);
    map*)
    
let remove ({ blockers } as sg) =
 [%spy "dev:constraint:remove" ~rid pp_stuck_goal sg];
 delayed := remove_from_list sg !delayed;
 blockers_map := List.fold_left (remove_blocked sg) !blockers_map blockers

let add ({ blockers } as sg) =
 [%spy "dev:constraint:add" ~rid pp_stuck_goal sg];
 delayed := sg :: !delayed;
 blockers_map := List.fold_left (append_blocked sg) !blockers_map blockers

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
  | _ -> assert false
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
  | _ -> assert false
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
  [%spy "dev:trail:undo" ~rid pp_trail !trail pp_string "->" pp_trail old_trail];
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

let print1 ?pp_ctx fmt x =
  let pp_depth fmt d =
    if d > 0 then
      Fmt.fprintf fmt "{%a} :@ "
        (pplist (uppterm ?pp_ctx d [] ~argsdepth:0 empty_env) " ") (C.mkinterval 0 d 0) in
  let pp_hyps fmt ctx =
    if ctx <> [] then
     Fmt.fprintf fmt "@[<hov 2>%a@]@ ?- "
      (pplist (fun fmt { hdepth = d; hsrc = t } ->
                 uppterm ?pp_ctx d [] ~argsdepth:0 empty_env fmt t) ", ") ctx in
  let pp_goal depth = uppterm ?pp_ctx depth [] ~argsdepth:0 empty_env in
  let { cdepth=depth;context=pdiff; conclusion=g }, blockers = x in
  Fmt.fprintf fmt " @[<h>@[<hov 2>%a%a%a@]@  /* suspended on %a */@]"
    pp_depth depth
    pp_hyps pdiff
    (pp_goal depth) g
    (pplist (uppterm ?pp_ctx 0 [] ~argsdepth:0 empty_env) ", ")
      (List.map (fun r -> UVar(r,0,0)) blockers)

let print_gid fmt x =
  let { cgid  = gid [@trace]; cdepth = _ }, _ = x in
  let () [@trace] = Fmt.fprintf fmt "%a" UUID.pp gid in
  ()

let print ?pp_ctx fmt x =
  pplist (print1 ?pp_ctx) " " fmt x

let pp_stuck_goal ?pp_ctx fmt { kind; blockers } = match kind with
   | Unification { adepth = ad; env = e; bdepth = bd; a; b } ->
      Fmt.fprintf fmt
       " @[<h>@[<hov 2>^%d:%a@ == ^%d:%a@]@  /* suspended on %a */@]"
        ad (uppterm ?pp_ctx ad [] ~argsdepth:0 empty_env) a
        bd (uppterm ?pp_ctx ad [] ~argsdepth:ad e) b
          (pplist ~boxed:false (uppterm ?pp_ctx 0 [] ~argsdepth:0 empty_env) ", ")
            (List.map (fun r -> UVar(r,0,0)) blockers)
   | Constraint c -> print ?pp_ctx fmt [c,blockers]
   | _ -> assert false

end (* }}} *)
module T  = ConstraintStoreAndTrail
module CS = ConstraintStoreAndTrail

(* Assigning an UVar wakes up suspended goals/constraints *)
let (@:=) r v =
  (T.trail_assignment[@inlined]) r;
  if uvar_is_a_blocker r then begin
    let blocked = CS.blocked_by r in
    [%spy "user:assign:resume" ~rid (fun fmt l ->
      let l = map_filter (function
        | { kind = Constraint { cgid; _ } ; _ } -> Some cgid
        | _ -> None) l in
      Fmt.fprintf fmt "%a" (pplist ~boxed:true UUID.pp " ") l) blocked];
    CS.to_resume :=
      List.fold_right
       (fun x acc -> if List.memq x acc then acc else x::acc) blocked
        !CS.to_resume
  end;
  r.contents <- v
;;

(* Low level, trail but no wakeup, used in freeze *)
let (@::==) r v =
  (T.trail_assignment[@inlined]) r;
  r.contents <- v

(******************************************************************************
  Unification (dereferencing and lift, to_heap)
 ******************************************************************************)

module HO : sig

  val unif : argsdepth:int -> matching:bool -> (UUID.t[@trace]) -> int -> env -> int -> term -> term -> bool

  (* lift/restriction/heapification with occur_check *)
  val move : 
    argsdepth:int -> env -> ?avoid:uvar_body ->
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

  val eta_contract_flex : depth:int -> term -> term option

  (* Put a flexible term in canonical expanded form: X^0 args.
   * It returns the canonical term and an assignment if needed.
   * (The first term is the result of dereferencing after the assignment) *)
  type assignment = uvar_body * int * term
  val expand_uv :
    depth:int -> uvar_body -> lvl:int -> ano:int -> term * assignment option
  val expand_appuv :
    depth:int -> uvar_body -> lvl:int -> args:term list -> term * assignment option

  val shift_bound_vars : depth:int -> to_:int -> term -> term

  val map_free_vars : map:constant C.Map.t -> depth:int -> to_:int -> term -> term

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
  | Some r1 ->
      (* It may be the case that in `X = Y` where `Y = f X` the term Y has to be
         moved/derefd in two steps, eg:
         
          else maux empty_env depth (deref_uv ~from:vardepth ~to_:(from+depth) args t)

         here maux carries the r1 = X (the ?avoid), while deref_uv does not, to avoid
         occur checking things twice. But deref_uv, if Y contains X, may assign
         X' to X (or x..\ X' x.. t oX). If this happens, then r1 is no more a dummy
         (unassigned variable) *)
        if !!r1 != C.dummy || r1 == r2 then raise RestrictionFailure

let rec make_lambdas destdepth args =
 if args <= 0 then
    UVar(oref C.dummy,destdepth,0)
 else
   Lam (make_lambdas (destdepth+1) (args-1))

let rec mknLam n x = if n = 0 then x else Lam (mknLam (n-1) x)

let mkAppUVar r lvl l =
  try UVar(r,lvl,in_fragment lvl l)
  with NotInTheFragment -> AppUVar(r,lvl,l)

let mkAppArg i fromdepth xxs' =
  try Arg(i,in_fragment fromdepth xxs')
  with NotInTheFragment -> AppArg (i,xxs')

let expand_uv r ~lvl ~ano =
  let args = C.mkinterval 0 (lvl+ano) 0 in
  if lvl = 0 then AppUVar(r,lvl,args), None else
  let r1 = oref C.dummy in
  let t = AppUVar(r1,0,args) in
  let assignment = mknLam ano t in
  t, Some (r,lvl,assignment)
let expand_uv ~depth r ~lvl ~ano =
  [%spy "dev:expand_uv:in" ~rid (uppterm depth [] ~argsdepth:0 empty_env) (UVar(r,lvl,ano))];
  let t, ass as rc = expand_uv r ~lvl ~ano in
  [%spy "dev:expand_uv:out" ~rid (uppterm depth [] ~argsdepth:0 empty_env) t (fun fmt -> function
    | None -> Fmt.fprintf fmt "no assignment"
    | Some (_,_,t) ->
        Fmt.fprintf fmt "%a := %a"
          (uppterm depth [] ~argsdepth:0 empty_env) (UVar(r,lvl,ano))
          (uppterm lvl [] ~argsdepth:0 empty_env) t) ass];
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
  [%spy "dev:expand_appuv:in" ~rid (uppterm depth [] ~argsdepth:0 empty_env) (AppUVar(r,lvl,args))];
  let t, ass as rc = expand_appuv r ~lvl ~args in
  [%spy "dev:expand_appuv:out" ~rid (uppterm depth [] ~argsdepth:0 empty_env) t (fun fmt -> function
    | None -> Fmt.fprintf fmt "no assignment"
    | Some (_,_,t) ->
        Fmt.fprintf fmt "%a := %a"
          (uppterm depth [] ~argsdepth:0 empty_env) (AppUVar(r,lvl,args))
          (uppterm lvl [] ~argsdepth:0 empty_env) t) ass];
  rc

let deoptimize_uv_w_args = function
  | UVar(r,lvl,args) when args > 0 ->
      AppUVar(r,lvl,C.mkinterval lvl args 0)
  | x -> x


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

let rec move ~argsdepth e ?avoid ~from ~to_ t =
(* TODO: to disable occur_check add something like: let avoid = None in *)
 let delta = from - to_ in
 let rc =
         if delta = 0 && e == empty_env && avoid == None then t (* Nothing to do! *)
 else begin
  (*if delta = 0 && e == empty_env && avoid <> None then prerr_endline "# EXPENSIVE OCCUR CHECK";*)
  let rec maux e depth x =
    [%trace "move" ~rid ("adepth:%d depth:%d from:%d to:%d x:%a"
        argsdepth depth from to_ (ppterm (from+depth) [] ~argsdepth e) x) begin
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
       let l' = smart_map3 maux e depth l in
       if t == t' && l == l' then x else App (c,t',l')
    | App (c,t,l) when c >= from ->
       App(c-delta, maux e depth t, smart_map3 maux e depth l)
    | App _ -> raise RestrictionFailure
    | Builtin (c,l) ->
       let l' = smart_map3 maux e depth l in
       if l == l' then x else Builtin (c,l')
    | CData _ -> x
    | Cons(hd,tl) ->
       let hd' = maux e depth hd in
       let tl' = maux e depth tl in
       if hd == hd' && tl == tl' then x else Cons(hd',tl')
    | Nil -> x
    | Discard when avoid = None -> x
    | Discard ->
       let r = oref C.dummy in
       UVar(r,to_,0)

    (* fast path with no deref... *)
    | UVar _ when delta == 0 && avoid == None -> x

    (* deref *)
    | UVar ({ contents = t }, vardepth, args) when t != C.dummy ->
       if depth == 0 then deref_uv ?avoid ~from:vardepth ~to_ args t
       else maux empty_env depth (deref_uv ~from:vardepth ~to_:(from+depth) args t)
    | AppUVar ({ contents = t }, vardepth, args) when t != C.dummy ->
       (* wrong, args escape occur check: if depth == 0 then deref_appuv ?avoid ~from:vardepth ~to_ args t
       else *) maux empty_env depth (deref_appuv ~from:vardepth ~to_:(from+depth) args t)
    | Arg (i, argsno) when e.(i) != C.dummy ->
       if to_ = argsdepth then deref_uv ?avoid ~from:argsdepth ~to_:(to_+depth) argsno e.(i)
       else
        let args = C.mkinterval from argsno 0 in
        let args =
        try smart_map3 maux e depth args
        with RestrictionFailure ->
          anomaly "move: could check if unrestrictable args are unused" in
       deref_appuv ?avoid ~from:argsdepth ~to_:(to_+depth) args e.(i)

    | AppArg(i, args) when e.(i) != C.dummy ->
       let args =
        try smart_map3 maux e depth args
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
        try smart_map (maux e depth) args
        with RestrictionFailure ->
         anomaly "TODO: implement deterministic restriction" in
       let r = oref C.dummy in
       let v = UVar(r,to_,0) in
       e.(i) <- v;
       mkAppUVar r to_ args
    | AppArg _ ->
       Fmt.fprintf Fmt.str_formatter
        "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
         (ppterm depth [] ~argsdepth e) x delta;
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
           let args = smart_map (maux empty_env depth) args in
           mkAppUVar r vardepth args
       else
         if vardepth + argsno <= to_ then x
         else
           let t, assignment = expand_uv ~depth:(from+depth) r ~lvl:vardepth ~ano:argsno in
           option_iter (fun (r,_,assignment) ->
              [%spy "user:assign:expand" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
               (uppterm (from+depth) [] ~argsdepth e) x
               (uppterm vardepth [] ~argsdepth e) assignment) ()];
              r @:= assignment) assignment;
           maux e depth t

    | AppUVar (r,vardepth,args) ->
       occurr_check avoid r;
       if delta < 0 then
         let r,vardepth,argsno =
           decrease_depth r ~from:vardepth ~to_:from 0 in
         let args0= C.mkinterval vardepth argsno 0 in
         let args =
          try smart_map (maux e depth) (args0@args)
          with RestrictionFailure -> anomaly "impossible, delta < 0" in
         mkAppUVar r vardepth args
       else if delta == 0 then
         AppUVar (r,vardepth,smart_map (maux e depth) args)
       else if List.for_all (deterministic_restriction e ~args_safe:(argsdepth=to_)) args then
          (* Code for deterministic restriction *)

          let pruned = ref (vardepth > to_) in
          let orig_argsno = List.length args in
          let filteredargs_vardepth = ref [] in
          let filteredargs_to =
            let rec filter i acc = function
              | [] -> filteredargs_vardepth := List.rev acc; []
              | arg :: args ->
                  try
                    let arg = maux e depth arg in
                    arg :: filter (succ i) (mkConst (vardepth + i) :: acc) args
                  with RestrictionFailure ->
                    pruned := true;
                    filter (succ i) acc args
            in
              filter 0 [] args in

          if !pruned then begin
            let vardepth' = min vardepth to_ in
            let r' = oref C.dummy in
            let newvar = mkAppUVar r' vardepth' !filteredargs_vardepth in
            let assignment = mknLam orig_argsno newvar in
            [%spy "user:assign:restrict" ~rid (fun fmt () -> Fmt.fprintf fmt "%d %a := %a" vardepth
               (ppterm (from+depth) [] ~argsdepth e) x
               (ppterm (vardepth) [] ~argsdepth e) assignment) ()];
            r @:= assignment;
            mkAppUVar r' vardepth' filteredargs_to
          end else
            mkAppUVar r vardepth filteredargs_to

       else begin
        Fmt.fprintf Fmt.str_formatter
         "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
          (ppterm depth [] ~argsdepth e) x delta;
        anomaly (Fmt.flush_str_formatter ())
       end
  end]
  in
   maux e 0 t
  end
 in
  [%spy "dev:move:out" ~rid (ppterm to_ [] ~argsdepth e) rc];
  rc

(* Hmove is like move for heap terms. By setting env to empty_env, it triggers
   fast paths in move (no need to heapify, the term already lives in the heap)*)
and hmove ?avoid ~from ~to_ t =
 [%trace "hmove" ~rid ("@[<hov 1>from:%d@ to:%d@ %a@]" from to_ (uppterm from [] ~argsdepth:0 empty_env) t) begin
   move ?avoid ~argsdepth:0 ~from ~to_ empty_env t
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
 [%trace "subst" ~rid ("@[<hov 2>fromdepth:%d t: %a@ ts: %a@]" fromdepth
   (uppterm (fromdepth) [] ~argsdepth:0 empty_env) t (pplist (uppterm fromdepth [] ~argsdepth:0 empty_env) ", ") ts)
 begin
 if ts == [] then t
 else
   let len = List.length ts in
   let fromdepthlen = fromdepth + len in
   let rec aux depth tt =
   [%trace "subst-aux" ~rid ("@[<hov 2>t: %a@]" (uppterm (fromdepth+1) [] ~argsdepth:0 empty_env) tt)
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
      let xs' = smart_map (aux depth) xs in
      let xxs' = x'::xs' in
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
        | Arg(i,0) -> mkAppArg i fromdepth xxs'
        | t ->
           let t = hmove ~from:fromdepth ~to_:(depth-len) t in
           beta (depth-len) [] t xxs'
      else if c < fromdepth then
        if x == x' && xs == xs' then orig else App(c,x',xs')
      else App(c-len,x',xs')
   | Builtin(c,xs) as orig ->
      let xs' = smart_map (aux depth) xs in
      if xs == xs' then orig else Builtin(c,xs')
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
       let args = smart_map (aux depth) args in
       mkAppUVar r vardepth args
   | AppUVar({ contents = t },vardepth,args) when t != C.dummy ->
      [%tcall aux depth (deref_appuv ~from:vardepth ~to_:depth args t)]
   | AppUVar(r,vardepth,args) ->
      let r,vardepth,argsno =
        decrease_depth r ~from:vardepth ~to_:fromdepth 0 in
      let args0 = C.mkinterval vardepth argsno 0 in
      let args = smart_map (aux depth) (args0@args) in
      mkAppUVar r vardepth args
   | Lam t -> Lam (aux (depth+1) t)
   | CData _ as x -> x
   end] in
     aux fromdepthlen t
 end]

and beta depth sub t args =
 [%trace "beta" ~rid ("@[<hov 2>subst@ t: %a@ args: %a@]"
     (uppterm (depth+List.length sub) [] ~argsdepth:0 empty_env) t
     (pplist (uppterm depth [] ~argsdepth:0 empty_env) ", ") args)
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
    [%spy "dev:subst:out" ~rid (ppterm depth [] ~argsdepth:0 empty_env) t'];
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
  [%trace "deref_uv" ~rid ("from:%d to:%d %a @@ %d"
      from to_ (ppterm from [] ~argsdepth:0 empty_env) t args) begin
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
     | UVar(t,depth,0) when from = depth ->
        UVar(t,depth,args')
     | AppUVar (r,depth,args2) ->
        let args = C.mkinterval from args' 0 in
        AppUVar (r,depth,args2 @ args)
     | UVar (r,vardepth,argsno) ->
        let args1 = C.mkinterval vardepth argsno 0 in
        let args2 = C.mkinterval from args' 0 in
        let args = args1 @ args2 in
        mkAppUVar r vardepth args
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
  [%spy "dev:is_llam" ~rid (fun fmt () -> let (b,map) = res in Fmt.fprintf fmt "%d + %a = %b, %a"
    lvl (pplist (ppterm adepth [] ~argsdepth:bdepth e) " ") args b
    (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%d |-> %d" x n) " ") map) ()];
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
let bind ~argsdepth r gamma l a d delta b left t e =
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
    [%spy "dev:bind:constant-mapping" ~rid (fun fmt () -> let (n,m) = c,n in Fmt.fprintf fmt
      "%d -> %d (c:%d b:%d gamma:%d delta:%d d:%d)" n m c b gamma delta d) ()];
    n in
  let rec bind b delta w t =
    [%trace "bind" ~rid ("%b gamma:%d + %a = t:%a a:%d delta:%d d:%d w:%d b:%d"
        left gamma (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%a |-> %d"
        (ppterm a [] ~argsdepth e) (mkConst x) n) " ") l
        (ppterm a [] ~argsdepth empty_env) t a delta d w b) begin
    match t with
    | UVar (r1,_,_) | AppUVar (r1,_,_) when r == r1 -> raise RestrictionFailure
    | Const c -> let n = cst c b delta in if n < 0 then mkConst n else Const n
    | Lam t -> Lam (bind b delta (w+1) t)
    | App (c,t,ts) -> App (cst c b delta, bind b delta w t, smart_map (bind b delta w) ts)
    | Cons(hd,tl) -> Cons(bind b delta w hd, bind b delta w tl)
    | Nil -> t
    | Builtin (c, tl) -> Builtin(c, smart_map (bind b delta w) tl)
    | CData _ -> t
    (* deref_uv *)
    | Arg (i,args) when e.(i) != C.dummy ->
        bind a 0 w (deref_uv ~from:argsdepth ~to_:(a+d+w) args e.(i))
    | AppArg (i,args) when e.(i) != C.dummy ->
        bind a 0 w (deref_appuv ~from:argsdepth ~to_:(a+d+w) args e.(i))
    | UVar ({ contents = t }, from, args) when t != C.dummy ->
        bind b delta w (deref_uv ~from ~to_:((if left then b else a)+d+w) args t)
    | AppUVar ({ contents = t }, from, args) when t != C.dummy ->
        bind b delta w (deref_appuv ~from ~to_:((if left then b else a)+d+w) args t)
    (* pruning *)
    | (UVar _ | AppUVar _ | Arg _ | AppArg _ | Discard) as orig ->
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
          | Discard ->
              let r = oref C.dummy in
              r, a+d+w, (true,[]), []
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
        [%spy "dev:bind:maybe-prune" ~rid (fun fmt () ->
           Fmt.fprintf fmt "lvl:%d is_llam:%b args:%a orig_args:%a orig:%a"
             lvl is_llam
             (pplist (fun fmt (x,n) ->
                Fmt.fprintf fmt "%a->%d" (ppterm a [] ~argsdepth:b e) (mkConst x) n) " ") args
             (pplist (ppterm a [] ~argsdepth e) " ") orig_args
             (ppterm a [] ~argsdepth e) orig) ()];
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
              List.split (keep_cst_for_lvl (List.sort Stdlib.compare l)) in
            let r' = oref C.dummy in
            r @:= mknLam n_args (mkAppUVar r' gamma args_gamma_lvl_abs);
            mkAppUVar r' gamma args_gamma_lvl_here
          else
            (* given that we need to make lambdas to prune some args,
             * we also permute to make the restricted meta eventually
             * fall inside the small fragment (sort the args) *)
            let args = List.sort Stdlib.compare args in
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
              mkAppUVar r lvl (smart_map (bind b delta w) orig_args)
            else
              (* we need to project away some of the args *)
              let r' = oref C.dummy in
              let v = mkAppUVar r' lvl args_lvl in
              r @:= mknLam n_args v;
              (* This should be the beta reduct. One could also
               * return the non reduced but bound as in the other if branch *)
              mkAppUVar r' lvl args_here
        end else begin
          mkAppUVar r lvl (smart_map (bind b delta w) orig_args)
        end
  end] in
    let v = mknLam new_lams (bind b delta 0 t) in
    [%spy "user:assign:HO" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
        (uppterm gamma [] ~argsdepth e) (UVar(r,gamma,0))
        (uppterm gamma [] ~argsdepth e) v) ()];
    r @:= v;
    true
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

let rec deref_head ~depth = function
  | UVar ({ contents = t }, from, ano)
    when t != C.dummy ->
      deref_head ~depth (deref_uv ~from ~to_:depth ano t)
  | AppUVar ({contents = t}, from, args)
    when t != C.dummy ->
      deref_head ~depth (deref_appuv ~from ~to_:depth args t)
  | x -> x

(* constant x occurs in term t with level d? *)
let occurs x d adepth e t =
  let rec aux d t = match deref_head ~depth:d t with
    | Const c -> c = x
    | Lam t -> aux (d+1) t
    | App (c, v, vs) -> c = x || aux d v || auxs d vs
    | UVar (r, lvl, ano) ->
       let t, assignment = expand_uv ~depth:d r ~lvl ~ano in
       option_iter (fun (r,_,assignment) -> r @:= assignment) assignment;
       aux d t
    | AppUVar (_, _, args) -> auxs d args
    | Builtin (_, vs) -> auxs d vs
    | Cons (v1, v2) -> aux d v1 || aux d v2
    | Arg(i,args) when e.(i) != C.dummy ->
      aux d (deref_uv ~from:adepth ~to_:d args e.(i))
    | AppArg(i,args) when e.(i) != C.dummy ->
      aux d (deref_appuv ~from:adepth ~to_:d args e.(i))
    | Nil | CData _ | Discard | Arg _ | AppArg _ -> false
  and auxs d = function
    | [] -> false
    | t :: ts -> aux d t || auxs d ts
  in
  x < d && aux d t

let rec eta_contract_args ~orig_depth ~depth r args eat ~argsdepth e =
  match args, eat with
  | _, [] -> [%spy "eta_contract_flex" ~rid (fun fmt () -> Fmt.fprintf fmt "all eaten") ()];
      begin
        try Some (AppUVar(r,0,smart_map (move ~argsdepth ~from:depth ~to_:orig_depth e) (List.rev args)))
        with RestrictionFailure -> None
      end
  | Const x::xs, y::ys when x == y && not (List.exists (occurs y depth argsdepth e) xs) ->
      [%spy "eta_contract_flex" ~rid (fun fmt -> Fmt.fprintf fmt "eat %d") y];
      eta_contract_args ~orig_depth ~depth r xs ys ~argsdepth e 
  | _, y::_ ->
      [%spy "eta_contract_flex" ~rid (fun fmt -> Fmt.fprintf fmt "cannot eat %d") y];
      None
;;

let rec eta_contract_flex orig_depth depth xdepth ~argsdepth e t eat =
  [%trace "eta_contract_flex" ~rid ("@[<hov 2>eta_contract_flex %d+%d:%a <- [%a]%!"
  xdepth depth (ppterm (xdepth+depth) [] ~argsdepth e) t
  (pplist (fun fmt i -> Fmt.fprintf fmt "%d" i) " ") eat) begin
  match deref_head ~depth:(xdepth+depth) t with
  | AppUVar(r,0,args) ->
      eta_contract_args ~orig_depth:(xdepth+orig_depth) ~depth:(xdepth+depth) r (List.rev args) eat ~argsdepth e
  | Lam t -> eta_contract_flex orig_depth (depth+1) xdepth ~argsdepth e t (depth+xdepth::eat)
  | UVar(r,lvl,ano) ->
      let t, assignment = expand_uv ~depth r ~lvl ~ano in
      option_iter (fun (r,_,assignment) -> r @:= assignment) assignment;
      eta_contract_flex orig_depth depth xdepth ~argsdepth e t eat
  | AppUVar(r,lvl,args) ->
      let t, assignment = expand_appuv ~depth r ~lvl ~args in
      option_iter (fun (r,_,assignment) -> r @:= assignment) assignment;
      eta_contract_flex orig_depth depth xdepth ~argsdepth e t eat
  | Arg (i, args) when e.(i) != C.dummy ->
      eta_contract_flex orig_depth depth xdepth ~argsdepth e
        (deref_uv ~from:argsdepth ~to_:(xdepth+depth) args e.(i)) eat
  | AppArg(i, args) when e.(i) != C.dummy ->
      eta_contract_flex orig_depth depth xdepth ~argsdepth e
        (deref_appuv ~from:argsdepth ~to_:(xdepth+depth) args e.(i)) eat
  | Arg (i, args) ->
      let to_ = argsdepth in
      let r = oref C.dummy in
      let v = UVar(r,to_,0) in
      e.(i) <- v;
      eta_contract_flex orig_depth depth xdepth ~argsdepth e
        (if args == 0 then v else UVar(r,to_,args)) eat
   | AppArg(i, args) ->
      let to_ = argsdepth in
      let r = oref C.dummy in
      let v = UVar(r,to_,0) in
      e.(i) <- v;
      eta_contract_flex orig_depth depth xdepth ~argsdepth e
        (mkAppUVar r to_ args) eat
  | _ -> None
   end]
;;
let eta_contract_flex depth xdepth ~argsdepth e t =
  eta_contract_flex depth depth xdepth ~argsdepth e t []
  [@@inline]

let isLam = function Lam _ -> true | _ -> false
  
let rec unif argsdepth matching depth adepth a bdepth b e =
   [%trace "unif" ~rid ("@[<hov 2>^%d:%a@ =%d%s= ^%d:%a@]%!"
       adepth (ppterm (adepth+depth) [] ~argsdepth empty_env) a
       depth (if matching then "m" else "")
       bdepth (ppterm (bdepth+depth) [] ~argsdepth:bdepth e) b)
   begin
   let delta = adepth - bdepth in
         
   (delta = 0 && a == b) || match a,b with
    | (Discard, _ | _, Discard) -> true

   (* _ as X binding *)
   | _, App(c,arg,[as_this]) when c == Global_symbols.asc ->
      unif argsdepth matching depth adepth a bdepth arg e &&
      unif argsdepth matching depth adepth a bdepth as_this e
   | _, App(c,arg,_) when c == Global_symbols.asc -> error "syntax error in as"
   | App(c,arg,_), _ when c == Global_symbols.asc ->
      unif argsdepth matching depth adepth arg bdepth b e

(* TODO: test if it is better to deref_uv first or not, i.e. the relative order
   of the clauses below *)
   | UVar(r1,_,args1), UVar(r2,_,args2)
     when r1 == r2 && !!r1 == C.dummy -> args1 == args2
     (* XXX this would be a type error *)
   | UVar(r1,vd,xs), AppUVar(r2,_,ys)
     when r1 == r2 && !!r1 == C.dummy -> unif argsdepth matching depth adepth (AppUVar(r1,vd,C.mkinterval vd xs 0)) bdepth b e
   | AppUVar(r1,vd,xs), UVar(r2,_,ys)
     when r1 == r2 && !!r1 == C.dummy -> unif argsdepth matching depth adepth a bdepth (AppUVar(r1,vd,C.mkinterval vd ys 0)) e
   | AppUVar(r1,vd,xs), AppUVar(r2,_,ys)
     when r1 == r2 && !!r1 == C.dummy ->
       let pruned = ref false in
       let filtered_args_rev = fold_left2i (fun i args x y ->
         let b = unif argsdepth matching depth adepth x bdepth y e in
         if not b then (pruned := true; args)
         else x :: args
         ) [] xs ys in
       if !pruned then begin
         let len = List.length xs in
         let r = oref C.dummy in
         r1 @:= mknLam len (mkAppUVar r vd (List.rev filtered_args_rev));
       end;
       true

   (* deref_uv *)
   | UVar ({ contents = t }, from, args), _ when t != C.dummy ->
      unif argsdepth matching depth adepth (deref_uv ~from ~to_:(adepth+depth) args t) bdepth b e
   | AppUVar ({ contents = t }, from, args), _ when t != C.dummy ->
      unif argsdepth matching depth adepth (deref_appuv ~from ~to_:(adepth+depth) args t) bdepth b e
   | _, UVar ({ contents = t }, from, args) when t != C.dummy ->
      unif argsdepth matching depth adepth a bdepth (deref_uv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, AppUVar ({ contents = t }, from, args) when t != C.dummy ->
      unif argsdepth matching depth adepth a bdepth (deref_appuv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, Arg (i,args) when e.(i) != C.dummy ->
      (* e.(i) is a heap term living at argsdepth wich can be > bdepth (e.g.
         the clause is at 0 and we are under a pi x\. As a result we do the
         deref to and the rec call at adepth *)
      unif argsdepth matching depth adepth a adepth
        (deref_uv ~from:argsdepth ~to_:(adepth+depth) args e.(i)) empty_env
   | _, AppArg (i,args) when e.(i) != C.dummy ->
      (* e.(i) is a heap term living at argsdepth wich can be > bdepth (e.g.
         the clause is at 0 and we are under a pi x\. As a result we do the
         deref to and the rec call at adepth *)
      let args =
        smart_map (move ~argsdepth ~from:bdepth ~to_:adepth e) args in
      unif argsdepth matching depth adepth a adepth
        (deref_appuv ~from:argsdepth ~to_:(adepth+depth) args e.(i)) empty_env

   (* UVar introspection (matching) *)
   | (UVar _ | AppUVar _), Const c when c == Global_symbols.uvarc && matching -> true
   | UVar(r,vd,ano), App(c,hd,[]) when c == Global_symbols.uvarc && matching ->
      unif argsdepth matching depth adepth (UVar(r,vd,ano)) bdepth hd e
   | AppUVar(r,vd,_), App(c,hd,[]) when c == Global_symbols.uvarc && matching ->
      unif argsdepth matching depth adepth (UVar(r,vd,0)) bdepth hd e
   | UVar(r,vd,ano), App(c,hd,[arg]) when c == Global_symbols.uvarc && matching ->
      let r_exp = oref C.dummy in
      let exp = UVar(r_exp,0,0) in
      r @:= UVar(r_exp,0,vd);
      unif argsdepth matching depth adepth exp bdepth hd e &&
      let args = list_to_lp_list (C.mkinterval 0 (vd+ano) 0) in
      unif argsdepth matching depth adepth args bdepth arg e
   | AppUVar(r,vd,args), App(c,hd,[arg]) when c == Global_symbols.uvarc && matching ->
      let r_exp = oref C.dummy in
      let exp = UVar(r_exp,0,0) in
      r @:= UVar(r_exp,0,vd);
      unif argsdepth matching depth adepth exp bdepth hd e &&
      let args = list_to_lp_list (C.mkinterval 0 vd 0 @ args) in
      unif argsdepth matching depth adepth args bdepth arg e
   | Lam _, (Const c | App(c,_,_)) when  c == Global_symbols.uvarc && matching ->
      begin match eta_contract_flex depth adepth ~argsdepth:adepth e a with
      | None -> false
      | Some a -> unif argsdepth matching depth adepth a bdepth b e
      end
   | (App _ | Const _ | Builtin _ | Nil | Cons _ | CData _), (Const c | App(c,_,[])) when c == Global_symbols.uvarc && matching -> false

   (* On purpose we let the fully applied uvarc pass, so that at the
    * meta level one can unify fronzen constants. One can use the var builtin
    * to discriminate the two cases, as in "p (uvar F L as X) :- var X, .." *)
   (* assign *)
   | _, Arg (i,0) ->
     begin try
      let v = hmove ~from:(adepth+depth) ~to_:argsdepth a in
      [%spy "user:assign" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
          (uppterm adepth [] ~argsdepth e) b (uppterm adepth [] ~argsdepth e) v) ()];
      e.(i) <- v;
      true
     with RestrictionFailure -> false end
   | UVar(r1,_,0), UVar (r2,_,0) when uvar_isnt_a_blocker r1 && uvar_is_a_blocker r2 -> unif argsdepth matching depth bdepth b adepth a e
   | AppUVar(r1,_,_), UVar (r2,_,0) when uvar_isnt_a_blocker r1 && uvar_is_a_blocker r2 -> unif argsdepth matching depth bdepth b adepth a e
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
         [%spy "user:assign" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
           (uppterm depth [] ~argsdepth e) b
           (uppterm depth [] ~argsdepth e) t) ()];
         r @:= t;
         true
       with RestrictionFailure when isLam a ->
          (* avoid fail occur-check on: x\A x = A  | x\y\A y x = A
             we eta expand and see how it is under the lambdas *)
          let b = (mkLam @@ mkAppUVar r origdepth [mkConst @@ depth + bdepth]) in
          let a = hmove ~from:(adepth+depth) ~to_:(bdepth+depth) a in
          unif argsdepth matching depth bdepth a bdepth b e
       | RestrictionFailure -> false
       end
   | UVar (r,origdepth,0), _ when not matching ->
       begin try
         let t =
           if depth=0 then
             move ~avoid:r ~argsdepth ~from:bdepth ~to_:origdepth e b
           else
             (* First step: we lift the r.h.s. to the l.h.s. level *)
             let b = move ~avoid:r ~argsdepth ~from:(bdepth+depth) ~to_:(adepth+depth) e b in
             (* Second step: we restrict the r.h.s. *)
             hmove ~from:(adepth+depth) ~to_:origdepth b in
         [%spy "user:assign" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
           (uppterm origdepth [] ~argsdepth:0 empty_env) a
           (uppterm origdepth [] ~argsdepth:0 empty_env) t) ()];
         r @:= t;
         true
       with RestrictionFailure when isLam b ->
          (* avoid fail occur-check on: x\A x = A  | x\y\A y x = A
             we eta expand and see how it is under the lambdas *)
          let a = (mkLam @@ mkAppUVar r origdepth [mkConst @@ depth + adepth]) in
          let b = move ~argsdepth ~from:(bdepth+depth) ~to_:(adepth+depth) e b in
          unif argsdepth matching depth adepth a adepth b e
       | RestrictionFailure -> false
       end

   (* XXX simplify either generated UVar(_,_,0) or AppUVar XXX *)
  | _, Arg (i,args) ->
      let v = make_lambdas adepth (args - depth) in
      [%spy "user:assign:simplify:stack:arg" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
        (uppterm depth [] ~argsdepth e) (Arg(i,0))
        (uppterm depth [] ~argsdepth e) v) ()];
      e.(i) <- v;
      let bdepth = adepth in (* like in deref for arg *)
      let b = deoptimize_uv_w_args @@ deref_uv ~from:argsdepth ~to_:(bdepth+depth) args v in
      unif argsdepth matching depth adepth a bdepth b e
   | UVar(r1,_,a1), UVar (r2,_,a2) when uvar_isnt_a_blocker r1 && uvar_is_a_blocker r2 && a1 + a2 > 0 -> unif argsdepth matching depth bdepth b adepth a e (* TODO argsdepth *)
   | AppUVar(r1,_,_), UVar (r2,_,a2) when uvar_isnt_a_blocker r1 && uvar_is_a_blocker r2 && a2 > 0 -> unif argsdepth matching depth bdepth b adepth a e

   | _, UVar (r,origdepth,args) when args > 0 && match a with UVar(r1,_,_) | AppUVar(r1,_,_) -> r != r1 | _ -> true ->
      let v = make_lambdas origdepth (args - depth) in
      [%spy "user:assign:simplify:stack:uvar" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
        (uppterm depth [] ~argsdepth e) (UVar(r,origdepth,0))
        (uppterm depth [] ~argsdepth e) v) ()];
      r @:= v;
      let b = deoptimize_uv_w_args @@ deref_uv ~from:origdepth ~to_:(bdepth+depth) args v in
      unif argsdepth matching depth adepth a bdepth b e
   | UVar (r,origdepth,args), _ when args > 0 && match b with UVar(r1,_,_) | AppUVar(r1,_,_) -> r != r1 | _ -> true ->
      let v = make_lambdas origdepth (args - depth) in
      [%spy "user:assign:simplify:heap" ~rid (fun fmt () -> Fmt.fprintf fmt "%a := %a"
         (uppterm depth [] ~argsdepth e) (UVar(r,origdepth,0))
         (uppterm depth [] ~argsdepth e) v) ()];
      r @:= v;
      let a = deoptimize_uv_w_args @@ deref_uv ~from:origdepth ~to_:(adepth+depth) args v in
      unif argsdepth matching depth adepth a bdepth b e

   (* HO *)
   | other, AppArg(i,args) ->
       let is_llam, args = is_llam adepth args adepth bdepth depth false e in
       if is_llam then
         let r = oref C.dummy in
         e.(i) <- UVar(r,adepth,0);
         try bind ~argsdepth r adepth args adepth depth delta bdepth false other e
         with RestrictionFailure -> false
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!"
         (uppterm depth [] ~argsdepth empty_env) a (uppterm depth [] ~argsdepth e) b ;
       let r = oref C.dummy in
       e.(i) <- UVar(r,adepth,0);
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers =
         match is_flex ~depth:(adepth+depth) other with
         | None -> [r]
         | Some r' -> if r==r' then [r] else [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else error (error_msg_hard_unif a b)
   | AppUVar(r2,_,_), (AppUVar (r1,_,_) | UVar (r1,_,_)) when uvar_isnt_a_blocker r1 && uvar_is_a_blocker r2 ->
       unif argsdepth matching depth bdepth b adepth a e
   | AppUVar (r, lvl,(args as oargs)), other when not matching ->
       let is_llam, args = is_llam lvl args adepth bdepth depth true e in
       if is_llam then
         try bind ~argsdepth r lvl args adepth depth delta bdepth true other e
         with RestrictionFailure when isLam other ->
          let a = mkLam @@ mkAppUVar r lvl (smart_map (move ~argsdepth e ~from:(depth+adepth) ~to_:(depth+adepth+1)) oargs @ [mkConst @@ depth + adepth]) in
          let b = move ~from:(depth+bdepth) ~to_:(depth+adepth) ~argsdepth e b in
          unif argsdepth matching depth adepth a adepth b e
         | RestrictionFailure -> false
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!"
         (uppterm depth [] ~argsdepth empty_env) a (uppterm depth [] ~argsdepth empty_env) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers = match is_flex ~depth:(bdepth+depth) other with | None -> [r] | Some r' -> [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else error (error_msg_hard_unif a b)
   | other, AppUVar (r, lvl,(args as oargs)) ->
       let is_llam, args = is_llam lvl args adepth bdepth depth false e in
       if is_llam then
         try bind ~argsdepth r lvl args adepth depth delta bdepth false other e
         with RestrictionFailure when isLam other ->
          let b = mkLam @@ mkAppUVar r lvl (smart_map (move ~argsdepth e ~from:(depth+bdepth) ~to_:(depth+bdepth+1)) oargs @ [mkConst @@ depth + bdepth]) in
          let a = hmove ~from:(depth+adepth) ~to_:(depth+bdepth) a in
          unif argsdepth matching depth bdepth a bdepth b e
         | RestrictionFailure -> false
        else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!"
         (uppterm depth [] ~argsdepth empty_env) a (uppterm depth [] ~argsdepth e) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b; matching} in
       let blockers =
         match is_flex ~depth:(adepth+depth) other with
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
       (delta=0 && x2 == y2 || unif argsdepth matching depth adepth x2 bdepth y2 e) &&
       for_all2 (fun x y -> unif argsdepth matching depth adepth x bdepth y e) xs ys
   | Builtin (c1,xs), Builtin (c2,ys) ->
       (* Inefficient comparison *)
       c1 = c2 && for_all2 (fun x y -> unif argsdepth matching depth adepth x bdepth y e) xs ys
   | Lam t1, Lam t2 -> unif argsdepth matching (depth+1) adepth t1 bdepth t2 e
   | Const c1, Const c2 ->
      if c1 < bdepth then c1=c2 else c1 >= adepth && c1 = c2 + delta
   (*| Const c1, Const c2 when c1 < bdepth -> c1=c2
     | Const c, Const _ when c >= bdepth && c < adepth -> false
     | Const c1, Const c2 when c1 = c2 + delta -> true*)
   | CData d1, CData d2 -> CData.equal d1 d2
   | Cons(hd1,tl1), Cons(hd2,tl2) ->
       unif argsdepth matching depth adepth hd1 bdepth hd2 e && unif argsdepth matching depth adepth tl1 bdepth tl2 e
   | Nil, Nil -> true

   (* eta *)
   | Lam t, Const c ->
       eta_expand_stack argsdepth matching depth adepth t bdepth b c [] e
   | Const c, Lam t ->
       eta_expand_heap argsdepth matching depth adepth c [] bdepth b t e
   | Lam t, App (c,x,xs) ->
       eta_expand_stack argsdepth matching depth adepth t bdepth b c (x::xs) e
   | App (c,x,xs), Lam t ->
       eta_expand_heap argsdepth matching depth adepth c (x::xs) bdepth b t e

   | _ -> false
   end]
and eta_expand_stack argsdepth matching depth adepth x bdepth b c args e =
  let extra = mkConst (bdepth+depth) in
  let motion = move ~argsdepth ~from:(bdepth+depth) ~to_:(bdepth+depth+1) e in
  let args = smart_map motion args in
  let eta = C.mkAppL c (args @ [extra]) in
  unif argsdepth matching (depth+1) adepth x bdepth eta e
and eta_expand_heap argsdepth matching depth adepth c args bdepth b x e =
  let extra = mkConst (adepth+depth) in
  let motion = hmove ~from:(adepth+depth) ~to_:(adepth+depth+1) in
  let args = smart_map motion args in
  let eta= C.mkAppL c (args @ [extra]) in
  unif argsdepth matching (depth+1) adepth eta bdepth x e

;;

(* FISSA PRECEDENZA PER AS e FISSA INDEXING per AS e fai coso generale in unif *)

let unif ~argsdepth ~matching (gid[@trace]) adepth e bdepth a b =
 let res = unif argsdepth matching 0 adepth a bdepth b e in
 [%spy "dev:unif:out" ~rid Fmt.pp_print_bool res];
 [%spy "user:backchain:fail-to" ~rid ~gid ~cond:(not res) (fun fmt () ->
     let op = if matching then "match" else "unify" in
     Fmt.fprintf fmt "@[<hov 2>%s@ %a@ with@ %a@]" op
       (uppterm (adepth) [] ~argsdepth:bdepth empty_env) a
       (uppterm (bdepth) [] ~argsdepth:bdepth e) b) ()];
 res
;;

(* Look in Git for Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower. *)

(* }}} *)

let full_deref ~adepth env ~depth t =
  let rec deref d = function
  | Const _ as x -> x
  | Lam r as orig ->
      let r' = deref (d+1) r in
      if r == r' then orig
      else Lam r'
  | App (n,x,xs) as orig ->
      let x' = deref d x in
      let xs' = smart_map (deref d) xs in
      if x == x' && xs == xs' then orig
      else App(n, x', xs')
  | Cons(hd,tl) as orig ->
      let hd' = deref d hd in
      let tl' = deref d tl in
      if hd == hd' && tl == tl' then orig
      else Cons(hd', tl')
  | Nil as x -> x
  | Discard as x -> x
  | Arg (i,ano) when env.(i) != C.dummy ->
      deref d (deref_uv ~from:adepth ~to_:d ano env.(i))
  | Arg _ as x -> x
  | AppArg (i,args) when env.(i) != C.dummy ->
      deref d (deref_appuv ~from:adepth ~to_:d args env.(i))
  | AppArg (i,args) as orig ->
      let args' = smart_map (deref d) args in
      if args == args' then orig
      else AppArg (i, args')
  | UVar (r,lvl,ano) when !!r != C.dummy ->
      deref d (deref_uv ~from:lvl ~to_:d ano !!r)
  | UVar _ as x -> x
  | AppUVar (r,lvl,args) when !!r != C.dummy ->
      deref d (deref_appuv ~from:lvl ~to_:d args !!r)
  | AppUVar (r,lvl,args) as orig ->
      let args' = smart_map (deref d) args in
      if args == args' then orig
      else AppUVar (r,lvl,args')
  | Builtin(c,xs) as orig ->
      let xs' = smart_map (deref d) xs in
      if xs == xs' then orig
      else Builtin(c,xs')
  | CData _ as x -> x
  in
    deref depth t

type assignment = uvar_body * int * term

let shift_bound_vars ~depth ~to_ t =
  let shift_db d n =
    if n < depth then n
    else n + to_ - depth in
  let rec shift d = function
  | Const n as x -> let m = shift_db d n in if m = n then x else mkConst m
  | Lam r as orig ->
     let r' = shift (d+1) r in
     if r == r' then orig
     else Lam r'
  | App (n,x,xs) as orig ->
      let x' = shift d x in
      let xs' = smart_map (shift d) xs in
      if x == x' && xs == xs' then orig
      else App(shift_db d n, x', xs')
  | Cons(hd,tl) as orig ->
      let hd' = shift d hd in
      let tl' = shift d tl in
      if hd == hd' && tl == tl' then orig
      else Cons(hd', tl')
  | Nil as x -> x
  | Discard as x -> x
  | Arg _ as x -> x
  | AppArg (i,args) as orig ->
      let args' = smart_map (shift d) args in
      if args == args' then orig
      else AppArg (i, args')
  | (UVar (r,_,_) | AppUVar(r,_,_)) when !!r != C.dummy ->
      anomaly "shift_bound_vars: non-derefd term"
  | UVar _ as x -> x
  | AppUVar (r,lvl,args) as orig ->
      let args' = smart_map (shift d) args in
      if args == args' then orig
      else AppUVar (r,lvl,args')
  | Builtin(c,xs) as orig ->
      let xs' = smart_map (shift d) xs in
      if xs == xs' then orig
      else Builtin(c,xs')
  | CData _ as x -> x
  in
    if depth = to_ then t else shift depth t

let map_free_vars ~map ~depth ~to_ t =
  let shift_bound = depth - to_ in
  let shift_db d n =
    if n < 0 then n
    else if n < depth then try C.Map.find n map with Not_found ->
      error (Printf.sprintf "The term cannot be put in the desired context since it contains name: %s" @@ C.show n)
    else if n >= depth && n - depth <= d then n - shift_bound
    else
      error (Printf.sprintf "The term cannot be put in the desired context since it contains name: %s" @@ C.show n)
    in
  let rec shift d = function
  | Const n as x -> let m = shift_db d n in if m = n then x else mkConst m
  | Lam r as orig ->
     let r' = shift (d+1) r in
     if r == r' then orig
     else Lam r'
  | App (n,x,xs) as orig ->
      let x' = shift d x in
      let xs' = smart_map (shift d) xs in
      if x == x' && xs == xs' then orig
      else App(shift_db d n, x', xs')
  | Cons(hd,tl) as orig ->
      let hd' = shift d hd in
      let tl' = shift d tl in
      if hd == hd' && tl == tl' then orig
      else Cons(hd', tl')
  | Nil as x -> x
  | Discard as x -> x
  | Arg _ as x -> x
  | AppArg (i,args) as orig ->
    let args' = smart_map (shift d) args in
    if args == args' then orig
    else AppArg (i, args')
  | (UVar (r,_,_) | AppUVar(r,_,_)) when !!r != C.dummy ->
      anomaly "map_free_vars: non-derefd term"
  | UVar(r,lvl,ano) -> UVar(r,min lvl to_,ano)
  | AppUVar (r,lvl,args) -> AppUVar (r,min lvl to_,smart_map (shift d) args)
  | Builtin(c,xs) as orig ->
    let xs' = smart_map (shift d) xs in
    if xs == xs' then orig
    else Builtin(c,xs')
  | CData _ as x -> x
  in
    if depth = to_ && C.Map.is_empty map then t else shift 0 t

let eta_contract_flex ~depth t =
  eta_contract_flex depth 0 ~argsdepth:0 empty_env t
  [@@inline]

end
(* }}} *)
open HO

let _ = do_deref := deref_uv;;
let _ = do_app_deref := deref_appuv;;


(* Built-in predicates and their FFI *************************************** *)


module FFI = struct

let builtins : Data.BuiltInPredicate.builtin_table ref = Fork.new_local (Hashtbl.create 17)
let lookup c = Hashtbl.find !builtins c

let type_err ~depth bname n ty t =
  type_error begin
    "builtin " ^ bname ^ ": " ^
    (if n = 0 then "" else string_of_int n ^ "th argument: ") ^
    "expected " ^ ty ^ " got" ^
    match t with
    | None -> "_"
    | Some t ->
       match t with
       | CData c -> Format.asprintf " %s: %a" (CData.name c) (Pp.uppterm depth [] ~argsdepth:0 empty_env) t
       | _ -> Format.asprintf ":%a" (Pp.uppterm depth [] ~argsdepth:0 empty_env) t
  end

let wrap_type_err bname n f x =
  try f x
  with Conversion.TypeErr(ty,depth,t) -> type_err ~depth bname n (Conversion.show_ty_ast ty) (Some t)

let arity_err ~depth bname n t =
  type_error ("builtin " ^ bname ^ ": " ^
    match t with
    | None -> string_of_int n ^ "th argument is missing"
    | Some t -> "too many arguments at: " ^
                  Format.asprintf "%a" (Pp.uppterm depth [] ~argsdepth:0 empty_env) t)

let out_of_term ~depth readback n bname state t =
  match deref_head ~depth t with
  | Discard -> Data.BuiltInPredicate.Discard
  | _ -> Data.BuiltInPredicate.Keep

let in_of_term ~depth readback n bname state t =
  wrap_type_err bname n (readback ~depth state) t

let inout_of_term ~depth readback n bname state t =
  wrap_type_err bname n (readback ~depth state) t

let mk_out_assign ~depth embed bname state input v  output =
  match output, input with
  | None, Data.BuiltInPredicate.Discard -> state, []
  | Some _, Data.BuiltInPredicate.Discard -> state, [] (* We could warn that such output was generated without being required *)
  | Some t, Data.BuiltInPredicate.Keep ->
     let state, t, extra = embed ~depth state t in
     state, extra @ [Conversion.Unify(v,t)]
  | None, Data.BuiltInPredicate.Keep -> state, []

let mk_inout_assign ~depth embed bname state input v  output =
  match output with
  | None -> state, []
  | Some t ->
     let state, t, extra = embed ~depth state (Data.BuiltInPredicate.Data t) in
     state, extra @ [Conversion.Unify(v,t)]

let in_of_termC ~depth readback n bname hyps constraints state t =
  wrap_type_err bname n (readback ~depth hyps constraints state) t

let inout_of_termC  = in_of_termC

let mk_out_assignC ~depth embed bname hyps constraints state input v  output =
  match output, input with
  | None, Data.BuiltInPredicate.Discard -> state, []
  | Some _, Data.BuiltInPredicate.Discard -> state, [] (* We could warn that such output was generated without being required *)
  | Some t, Data.BuiltInPredicate.Keep ->
     let state, t, extra = embed ~depth hyps constraints state t in
     state, extra @ [Conversion.Unify(v,t)]
  | None, Data.BuiltInPredicate.Keep -> state, []

let mk_inout_assignC ~depth embed bname hyps constraints state input v  output =
  match output with
  | Some t ->
     let state, t, extra = embed ~depth hyps constraints state (Data.BuiltInPredicate.Data t) in
     state, extra @ [Conversion.Unify(v,t)]
  | None -> state, []

let map_acc f s l =
   let rec aux acc extra s = function
   | [] -> s, List.rev acc, List.(concat (rev extra))
   | x :: xs ->
       let s, x, gls = f s x in
       aux (x :: acc) (gls :: extra) s xs
   in
     aux [] [] s l

let call (Data.BuiltInPredicate.Pred(bname,ffi,compute)) ~once ~depth hyps constraints state data =
  let rec aux : type i o h c.
    (i,o,h,c) Data.BuiltInPredicate.ffi -> h -> c -> compute:i -> reduce:(State.t -> o -> State.t * Conversion.extra_goals) ->
       term list -> int -> State.t -> Conversion.extra_goals list -> State.t * Conversion.extra_goals =
  fun ffi ctx constraints ~compute ~reduce data n state extra ->
    match ffi, data with
    | Data.BuiltInPredicate.Easy _, [] ->
       let result = wrap_type_err bname 0 (fun () -> compute ~depth) () in
       let state, l = reduce state result in
       state, List.(concat (rev extra) @ rev l)
    | Data.BuiltInPredicate.Read _, [] ->
       let result = wrap_type_err bname 0 (compute ~depth ctx constraints) state in
       let state, l = reduce state result in
       state, List.(concat (rev extra) @ rev l)
    | Data.BuiltInPredicate.Full _, [] ->
       let state, result, gls = wrap_type_err bname 0 (compute ~depth ctx constraints) state in
       let state, l = reduce state result in
       state, List.(concat (rev extra)) @ gls @ List.rev l
    | Data.BuiltInPredicate.FullHO _, [] ->
       let state, result, gls = wrap_type_err bname 0 (compute ~once ~depth ctx constraints) state in
       let state, l = reduce state result in
       state, List.(concat (rev extra)) @ gls @ List.rev l
    | Data.BuiltInPredicate.VariadicIn(_,{ ContextualConversion.readback }, _), data ->
       let state, i, gls =
         map_acc (in_of_termC ~depth readback n bname ctx constraints) state data in
       let state, rest = wrap_type_err bname 0 (compute i ~depth ctx constraints) state in
       let state, l = reduce state rest in
       state, List.(gls @ concat (rev extra) @ rev l)
    | Data.BuiltInPredicate.VariadicOut(_,{ ContextualConversion.embed; readback }, _), data ->
       let i = List.map (out_of_term ~depth readback n bname state) data in
       let state, (rest, out) = wrap_type_err bname 0 (compute i ~depth ctx constraints) state in
       let state, l = reduce state rest in
       begin match out with
         | Some out ->
             let state, ass =
               map_acc3 (mk_out_assignC ~depth embed bname ctx constraints) state i data out in 
             state, List.(concat (rev extra) @ rev (concat ass) @ l)
         | None -> state, List.(concat (rev extra) @ rev l)
       end
    | Data.BuiltInPredicate.VariadicInOut(_,{ ContextualConversion.embed; readback }, _), data ->
       let state, i, gls =
         map_acc (inout_of_termC ~depth readback n bname ctx constraints) state data in
       let state, (rest, out) = wrap_type_err bname 0 (compute i ~depth ctx constraints) state in
       let state, l = reduce state rest in
       begin match out with
         | Some out ->
             let state, ass =
               map_acc3 (mk_inout_assignC ~depth embed bname ctx constraints) state i data out in 
             state, List.(gls @ concat (rev extra) @ rev (concat ass) @ l)
         | None -> state, List.(gls @ concat (rev extra) @ rev l)
       end
    | Data.BuiltInPredicate.CIn({ ContextualConversion.readback }, _, ffi), t :: rest ->
        let state, i, gls = in_of_termC ~depth readback n bname ctx constraints state t in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state (gls :: extra)
    | Data.BuiltInPredicate.COut({ ContextualConversion.embed; readback }, _, ffi), t :: rest ->
        let i = out_of_term ~depth readback n bname state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_out_assignC ~depth embed bname ctx constraints state i t out in
          state, ass @ l in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state extra
    | Data.BuiltInPredicate.CInOut({ ContextualConversion.embed; readback }, _, ffi), t :: rest ->
        let state, i, gls = inout_of_termC ~depth readback n bname ctx constraints state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_inout_assignC ~depth embed bname ctx constraints state i t out in
          state, ass @ l in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state (gls :: extra)
    | Data.BuiltInPredicate.In({ Conversion.readback }, _, ffi), t :: rest ->
        let state, i, gls = in_of_term ~depth readback n bname state t in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state (gls :: extra)
    | Data.BuiltInPredicate.Out({ Conversion.embed; readback }, _, ffi), t :: rest ->
        let i = out_of_term ~depth readback n bname state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_out_assign ~depth embed bname state i t out in
          state, ass @ l in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state extra
    | Data.BuiltInPredicate.InOut({ Conversion.embed; readback }, _, ffi), t :: rest ->
        let state, i, gls = inout_of_term ~depth readback n bname state t in
        let reduce state (rest, out) =
          let state, l = reduce state rest in
          let state, ass = mk_inout_assign ~depth embed bname state i t out in
          state, ass @ l in
        aux ffi ctx constraints ~compute:(compute i) ~reduce rest (n + 1) state (gls :: extra)

    | _, t :: _ -> arity_err ~depth bname n (Some t)
    | _, [] -> arity_err ~depth bname n None

  in
  let rec aux_ctx : type i o h c. (i,o,h,c) Data.BuiltInPredicate.ffi -> (h,c) ContextualConversion.ctx_readback = function
    | Data.BuiltInPredicate.FullHO(f,_) -> f
    | Data.BuiltInPredicate.Full(f,_) -> f
    | Data.BuiltInPredicate.Read(f,_) -> f
    | Data.BuiltInPredicate.VariadicIn(f,_,_) -> f
    | Data.BuiltInPredicate.VariadicOut(f,_,_) -> f
    | Data.BuiltInPredicate.VariadicInOut(f,_,_) -> f
    | Data.BuiltInPredicate.Easy _ -> ContextualConversion.unit_ctx
    | Data.BuiltInPredicate.In(_,_,rest) -> aux_ctx rest
    | Data.BuiltInPredicate.Out(_,_,rest) -> aux_ctx rest
    | Data.BuiltInPredicate.InOut(_,_,rest) -> aux_ctx rest
    | Data.BuiltInPredicate.CIn(_,_,rest) -> aux_ctx rest
    | Data.BuiltInPredicate.COut(_,_,rest) -> aux_ctx rest
    | Data.BuiltInPredicate.CInOut(_,_,rest) -> aux_ctx rest
  in
    let reduce state _ = state, [] in
    let state, ctx, csts, gls_ctx = aux_ctx ffi ~depth hyps constraints state in
    let state, gls = aux ffi ctx csts ~compute ~reduce data 1 state [] in
    state, gls_ctx @ gls
;;

end


(******************************************************************************
  Indexing
 ******************************************************************************)

module Indexing = struct (* {{{ *)

(* These are sorted wrt lex_insertion
 -2
 -1
  0
  1.-1
  1.-2
  1
  1.+2
  1.+1
  2

  The idea being that clause "a" to be inserted w.r.t. "b" takes
  as timestamp the one of "b" followerd by the timestamp. If "a"
  has to be before, the timestamp is made negative.
*)
let lex_insertion l1 l2 =
  let rec lex_insertion fst l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | x :: l1, y :: l2  when not fst ->
      let r =
        if x < 0 && y < 0 || x > 0 && y > 0
          then y - x else x - y in
      if r = 0 then lex_insertion false l1 l2
      else r
  | x1 :: l1, x2 :: l2 ->
      let x = x1 - x2 in
      if x = 0 then lex_insertion false l1 l2
      else x
  | [], ys -> lex_insertion false [0] ys
  | xs, [] -> lex_insertion false xs [0]
  in
  lex_insertion true l1 l2
let mustbevariablec = min_int (* uvar or uvar t or uvar l t *)

let ppclause f ~hd { depth; args = args; hyps = hyps } =
  Fmt.fprintf f "@[<hov 1>%a :- %a.@]"
     (uppterm ~min_prec:(Elpi_parser.Parser_config.appl_precedence+1) depth [] ~argsdepth:0 empty_env) (C.mkAppL hd args)
     (pplist (uppterm ~min_prec:(Elpi_parser.Parser_config.appl_precedence+1) depth [] ~argsdepth:0 empty_env) ", ") hyps

(** [tail_opt L] returns: [match L with [] -> [] | x :: xs -> xs] *)
let tail_opt = function
  | [] -> []
  | _ :: xs -> xs

let hd_opt = function
  | x :: _ -> Mode.get_head x
  | _ -> Output

type clause_arg_classification =
  | Variable
  | MustBeVariable
  | Rigid of constant * Mode.t

let rec classify_clause_arg ~depth matching t =
  match deref_head ~depth t with
  | Const k when k == Global_symbols.uvarc -> MustBeVariable
  | Const k -> Rigid(k,matching)
  | Nil -> Rigid (Global_symbols.nilc,matching)
  | Cons _ -> Rigid (Global_symbols.consc,matching)
  | App (k,_,_) when k == Global_symbols.uvarc -> MustBeVariable
  | App (k,a,_) when k == Global_symbols.asc -> classify_clause_arg ~depth matching a
  | (App (k,_,_) | Builtin (k,_)) -> Rigid (k,matching)
  | Lam _ -> Variable (* loose indexing to enable eta *)
  | Arg _ | UVar _ | AppArg _ | AppUVar _ | Discard -> Variable
  | CData d ->
     let hash = -(CData.hash d) in
     if hash > mustbevariablec then Rigid (hash,matching)
     else Rigid (hash+1,matching)

(** 
  [classify_clause_argno ~depth N mode L] where L is the arguments of the
  clause. Returns the classification of the Nth element of L wrt to the Nth mode
  for the TwoLevelIndex 
*)
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

(**
  Hashing function for clause and queries depending on the boolean [is_goal].
  This is done by hashing the parameters wrt to Sys.int_size - 1 (see [hash_bits])
*)
let hash_arg_list is_goal hd ~depth args mode spec =
  let nargs = List.(length (filter (fun x -> x > 0) spec)) in
  (* we partition equally, that may not be smart, but is simple ;-) *)
  let arg_size = hash_bits / nargs in
  let hash size k =
    let modulus = 1 lsl size in
    let kabs = Hashtbl.hash k in
    let h = kabs mod modulus in
    [%spy "dev:index:subhash-const" ~rid C.pp k pp_string (dec_to_bin2 h)];
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
  and aux_arg size mode deep arg =
    let h =
      match deref_head ~depth arg with
      | App (k,a,_) when k == Global_symbols.asc -> aux_arg size mode deep a
      | Const k when k == Global_symbols.uvarc ->
          hash size mustbevariablec
      | App(k,_,_) when k == Global_symbols.uvarc && deep = 1 ->
          hash size mustbevariablec
      | Const k -> hash size k
      | App(k,_,_) when deep = 1 -> hash size k
      | App(k,x,xs) ->
          let size = size / (List.length xs + 2) in
          let self = aux_arg size mode (deep-1) in
          let shift = shift size in
          (hash size k) lor
          (shift 1 (self x)) lor
          List.(fold_left (lor) 0 (mapi (fun i x -> shift (i+2) (self x)) xs))
      | (UVar _ | AppUVar _) when mode == Input && is_goal -> hash size mustbevariablec
      | (UVar _ | AppUVar _) when mode == Input -> all_1 size
      | (UVar _ | AppUVar _) -> if is_goal then all_0 size else all_1 size
      | (Arg _ | AppArg _) -> all_1 size
      | Nil -> hash size Global_symbols.nilc
      | Cons (x,xs) ->
          let size = size / 2 in
          let self = aux_arg size mode (deep-1) in
          let shift = shift size in
          (hash size Global_symbols.consc) lor (shift 1 (self x))
      | CData s -> hash size (CData.hash s)
      | Lam _ -> all_1 size
      | Discard -> all_1 size
      | Builtin(k,xs) ->
          let size = size / (List.length xs + 1) in
          let self = aux_arg size mode (deep-1) in
          let shift = shift size in
          (hash size k) lor
          List.(fold_left (lor) 0 (mapi (fun i x -> shift (i+1) (self x)) xs))
    in
    [%spy "dev:index:subhash" ~rid (fun fmt () ->
       Fmt.fprintf fmt "%s: %d: %s: %a"
         (if is_goal then "goal" else "clause")
         size
         (dec_to_bin2 h)
         (uppterm depth [] ~argsdepth:0 empty_env) arg) ()];
    h
  in
  let h = aux 0 0 args mode spec in
  [%spy "dev:index:hash" ~rid (fun fmt () ->
     Fmt.fprintf fmt "%s: %s: %a"
       (if is_goal then "goal" else "clause")
       (dec_to_bin2 h)
       (pplist ~boxed:true (uppterm depth [] ~argsdepth:0 empty_env) " ")
      (Const hd :: args)) ()];
  h

let hash_clause_arg_list = hash_arg_list false
let hash_goal_arg_list = hash_arg_list true

(*  returns the maximal length of any sub_list
    this operation is done at compile time per each clause being index
    for example the term (app['a','b',app['c','d','e'], 'f', app['a','b','c','d','e','f']])
    has three lists L1 = ['a','b',app['c','d','e'], 'f', app['a','b','c','d','e','f']
                    L2 = ['c','d','e']
                    L3 = app['a','b','c','d','e','f']
    and the longest one has length 6
*)
let rec max_list_length acc = function
  | Nil -> acc
  | Cons (a, (UVar (_, _, _) | AppUVar (_, _, _) | Arg (_, _) | AppArg (_, _) | Discard)) -> 
      let alen = max_list_length 0 a in
      max (acc+2) alen
  | Cons (a, b)-> 
      let alen = max_list_length 0 a in
      let blen = max_list_length (acc+1) b in 
      max blen alen
  | App (_,x,xs) -> List.fold_left (fun acc x -> max acc (max_list_length 0 x)) acc (x::xs)
  | Builtin (_, xs) -> List.fold_left (fun acc x -> max acc (max_list_length 0 x)) acc xs
  | Lam t -> max_list_length acc t
  | Discard | Const _ |CData _ | UVar (_, _, _) | AppUVar (_, _, _) | Arg (_, _) | AppArg (_, _) -> acc

let max_lists_length = List.fold_left (fun acc e -> max (max_list_length 0 e) acc) 0

(** 
  [arg_to_trie_path ~safe ~depth ~is_goal args arg_depths arg_modes mp max_list_length]
  returns the path represetation of a term to be used in indexing with trie.
  args, args_depths and arg_modes are the lists of respectively the arguments, the 
  depths and the modes of the current term to be indexed.
  ~is_goal is used to know if we are encoding the path for instance retriaval or 
  for clause insertion in the trie.
  In the former case, each argument we add a special mkInputMode/mkOutputMode 
  node before each argument to be indexed. This special node is used during 
  instance retrival to know the mode of the current argument
  - mp is the max_path size of any path in the index used to truncate the goal
  - max_list_length is the length of the longest sublist in each term of args 
*)
let arg_to_trie_path ~safe ~depth ~is_goal args arg_depths args_depths_ar mode mp (max_list_length':int) : Discrimination_tree.Path.t =
  let open Discrimination_tree in

  let path_length = mp + Array.length args_depths_ar + 1 in
  let path = Path.make path_length mkPathEnd in
  
  let current_ar_pos = ref 0 in
  let current_user_depth = ref 0 in
  let current_min_depth = ref max_int in
  let update_current_min_depth d = if not is_goal then current_min_depth := min !current_min_depth d in

  (* Invariant: !current_ar_pos < Array.length args_depths_ar *)
  let update_ar depth = 
    if not is_goal then begin
    let old_max = Array.unsafe_get args_depths_ar !current_ar_pos in
    let current_max = !current_user_depth - depth in
    if old_max < current_max then 
      Array.unsafe_set args_depths_ar !current_ar_pos current_max
    end
  in

  let rec list_to_trie_path ~safe ~depth ~h path_depth (len: int) (t: term) : unit =
    match deref_head ~depth t with
    | Nil -> Path.emit path mkListEnd; update_current_min_depth path_depth
    | Cons (a, b) ->
        (* heuristic: we limit the size of the list to at most 30 *)
        (*            this aims to control the width of the path, *)
        (*            or equivalently the number of children of   *)
        (*            a specific node.                            *)
        (* for example, the term `app[1,...,100]` with depth 2,   *)
        (*              has the node `app` with arity `1` as first*)
        (*              cell, then come the elment of the list    *)
        (*              up to the 30^th elemebt                   *)
        if is_goal && h >= max_list_length' then (Path.emit path mkListTailVariableUnif; update_current_min_depth path_depth)
        else
          (main ~safe ~depth a path_depth;
          list_to_trie_path ~depth ~safe ~h:(h+1) path_depth (len+1) b)
    
    (* These cases can come from terms like `[_ | _]`, `[_ | A]` ...  *)
    | UVar _ | AppUVar _ | Arg _ | AppArg _ | Discard -> Path.emit path mkListTailVariable; update_current_min_depth path_depth

    (* One could write the following: 
      type f list int.
      p [1,2,3,4 | f]. *)
    | App _ | Const _ -> Path.emit path mkListTailVariable; update_current_min_depth path_depth

    | Builtin _ | CData _ | Lam _ -> 
        type_error (Format.asprintf "[DT]: not a list: %a" (Pp.ppterm depth [] ~argsdepth:0 Data.empty_env) (deref_head ~depth t))

  and emit_mode is_goal mode = if is_goal then Path.emit path mode
  (** gives the path representation of a list of sub-terms *)
  and arg_to_trie_path_aux ~safe ~depth t_list path_depth : unit = 
    if path_depth = 0 then update_current_min_depth path_depth
    else 
      match t_list with 
      | [] -> update_current_min_depth path_depth
      | hd :: tl -> 
          main ~safe ~depth hd path_depth;
          arg_to_trie_path_aux ~safe ~depth tl path_depth
  (** gives the path representation of a term *)
  and main ~safe ~depth t path_depth : unit =
    if path_depth = 0 then update_current_min_depth path_depth
    else if is_goal && Path.get_builder_pos path >= path_length then 
      (Path.emit path mkAny; update_current_min_depth path_depth)
    else
      let path_depth = path_depth - 1 in 
      match deref_head ~depth t with 
      | Const k when k == Global_symbols.uvarc -> Path.emit path mkVariable; update_current_min_depth path_depth
      | Const k when safe -> Path.emit path @@ mkConstant ~safe ~data:k ~arity:0; update_current_min_depth path_depth
      | Const k -> Path.emit path @@ mkConstant ~safe ~data:k ~arity:0; update_current_min_depth path_depth
      | CData d -> Path.emit path @@ mkPrimitive d; update_current_min_depth path_depth
      | App (k,_,_) when k == Global_symbols.uvarc -> Path.emit path @@ mkVariable; update_current_min_depth path_depth
      | App (k,a,_) when k == Global_symbols.asc -> main ~safe ~depth a (path_depth+1)
      | Lam _ -> Path.emit path mkAny; update_current_min_depth path_depth (* loose indexing to enable eta *)
      | Arg _ | UVar _ | AppArg _ | AppUVar _ | Discard -> Path.emit path @@ mkVariable; update_current_min_depth path_depth
      | Builtin (k,tl) ->
        Path.emit path @@ mkConstant ~safe ~data:k ~arity:(if path_depth = 0 then 0 else List.length tl);
        arg_to_trie_path_aux ~safe ~depth tl path_depth
      | App (k, x, xs) -> 
        let arg_length = if path_depth = 0 then 0 else List.length xs + 1 in
        Path.emit path @@ mkConstant ~safe ~data:k ~arity:arg_length;
        main ~safe ~depth x path_depth;
        arg_to_trie_path_aux ~safe ~depth xs path_depth
      | Nil -> Path.emit path mkListHead; Path.emit path mkListEnd; update_current_min_depth path_depth
      | Cons (x,xs) ->
          Path.emit path mkListHead;
          main ~safe ~depth x (path_depth + 1);
          list_to_trie_path ~safe ~depth ~h:1 (path_depth + 1) 0 xs

  (** builds the sub-path of a sublist of arguments of the current clause  *)
  and make_sub_path arg_hd arg_tl arg_depth_hd arg_depth_tl (mode_hd:Mode.t) mode_tl = 
    emit_mode is_goal (match mode_hd with Input -> mkInputMode | _ -> mkOutputMode);
    begin 
      if not is_goal then begin
        current_user_depth := arg_depth_hd;
        current_min_depth := max_int;
        main ~safe ~depth arg_hd arg_depth_hd;
        update_ar !current_min_depth;
      end else main ~safe ~depth arg_hd (Array.unsafe_get args_depths_ar !current_ar_pos)
    end;
    incr current_ar_pos;
    aux ~safe ~depth is_goal arg_tl arg_depth_tl mode_tl

  (** main function: build the path of the arguments received in entry  *)
  and aux ~safe ~depth is_goal args arg_depths mode =
    match args, arg_depths, mode with 
    | _, [], _ -> ()
    | arg_hd :: arg_tl, arg_depth_hd :: arg_depth_tl, [] ->
      make_sub_path arg_hd arg_tl arg_depth_hd arg_depth_tl Output []
    | arg_hd :: arg_tl, arg_depth_hd :: arg_depth_tl, mode_hd :: mode_tl ->
      make_sub_path arg_hd arg_tl arg_depth_hd arg_depth_tl (Mode.get_head mode_hd) mode_tl 
    | _, _ :: _,_ -> anomaly "Invalid Index length" in
  begin
    if args == [] then emit_mode is_goal mkOutputMode
    else aux ~safe ~depth is_goal args (if is_goal then Array.to_list args_depths_ar else arg_depths) mode
  end;
  Path.stop path  

let make_new_Map_snd_level_index argno mode =
  TwoLevelIndex {
    argno;
    mode;
    all_clauses = Bl.empty ();
    flex_arg_clauses = Bl.empty ();
    arg_idx = Ptmap.empty;
  }
        
let add_clause_to_snd_lvl_idx ~depth ~insert predicate clause = function
  | TwoLevelIndex { all_clauses; argno; mode; flex_arg_clauses; arg_idx; } ->
    begin match classify_clause_argno ~depth argno mode clause.args with
    | Variable ->
      (* X: matches both rigid and flexible terms *)
      TwoLevelIndex {
        argno; mode;
        all_clauses = insert clause all_clauses;
        flex_arg_clauses = insert clause flex_arg_clauses;
        arg_idx = Ptmap.map (fun l_rev -> insert clause l_rev) arg_idx;
      }
    | MustBeVariable ->
      (* uvar: matches only flexible terms (or itself at the meta level) *)
      let clauses =
        try Ptmap.find mustbevariablec arg_idx
        with Not_found -> flex_arg_clauses in
      TwoLevelIndex {
          argno; mode;
        all_clauses = insert clause all_clauses;
        flex_arg_clauses;
        arg_idx = Ptmap.add mustbevariablec (insert clause clauses) arg_idx;
      }
    | Rigid (arg_hd,arg_mode) ->
      (* t: a rigid term matches flexible terms only in unification mode *)
      let clauses =
        try Ptmap.find arg_hd arg_idx
        with Not_found -> flex_arg_clauses in
      let all_clauses =
        if arg_mode = Input then all_clauses else insert clause all_clauses in
      TwoLevelIndex {
        argno; mode;
        all_clauses;
        flex_arg_clauses;
        arg_idx = Ptmap.add arg_hd (insert clause clauses) arg_idx;
      }
    end
| BitHash { mode; args; args_idx } ->
    let hash = hash_clause_arg_list predicate ~depth clause.args mode args in
    let clauses =
      try Ptmap.find hash args_idx
      with Not_found -> Bl.empty () in
    BitHash {
       mode; args;
       args_idx = Ptmap.add hash (insert clause clauses) args_idx
    }
| IndexWithDiscriminationTree {mode; arg_depths; args_idx; } ->
    let max_depths = Discrimination_tree.max_depths args_idx in
    let max_path = Discrimination_tree.max_path args_idx in
    let max_list_length = max_lists_length clause.args in
    (* Format.printf "[%d] Going to index [%a]\n%!" max_list_length (pplist pp_term ",") clause.args; *)
    let path = arg_to_trie_path ~depth ~safe:true ~is_goal:false clause.args arg_depths max_depths mode max_path max_list_length in
    [%spy "dev:disc-tree:depth-path" ~rid pp_string "Inst: MaxDepths " (pplist pp_int "") (Array.to_list max_depths)];
    let args_idx = Discrimination_tree.index args_idx path clause ~max_list_length in
    IndexWithDiscriminationTree {
      mode; arg_depths;
      args_idx = args_idx
    }

let compile_time_tick x = x + 1
let run_time_tick x = x - 1
    
let rec add1clause_runtime ~depth { idx; time; times } predicate clause =
  try
    let snd_lvl_idx = Ptmap.find predicate idx in
    let time = run_time_tick time in
    clause.timestamp <- [time];
    let snd_lvl_idx = add_clause_to_snd_lvl_idx ~depth ~insert:Bl.cons predicate clause snd_lvl_idx in
    { times; time; idx = Ptmap.add predicate snd_lvl_idx idx }
  with
  | Not_found ->
      (* Unknown predicate, we could detect this statically and forbid it *)
      let idx = Ptmap.add predicate (make_new_Map_snd_level_index 0 []) idx in
      add1clause_runtime ~depth { idx; time; times } predicate clause

let add_clauses ~depth clauses idx =
  (* pplist (fun fmt (hd, b) -> ppclause fmt hd b) ";" Fmt.std_formatter clauses; *)
  (* let t1 = Unix.gettimeofday () in *)
  let idx = List.fold_left (fun m (p,c) -> add1clause_runtime ~depth m p c) idx clauses in
  (* let t2 = Unix.gettimeofday () in  *)
  (* pp_string Fmt.std_formatter (Printf.sprintf "\nTime taken by add_clauses is %f\n" (t2-.t1)); *)
  idx
  
let add_clauses ~depth clauses clauses_src { index; src } =
  { index = add_clauses ~depth clauses index; src = List.rev clauses_src @ src }

let add_to_times loc name time predicate times =
  match name with
  | None -> times
  | Some id ->
    if StrMap.mem id times then
      error ?loc ("duplicate clause name " ^ id)
    else
      StrMap.add id (time,predicate) times

let time_of loc x times =
  try StrMap.find x times
  with Not_found -> error ?loc ("cannot graft, clause " ^ x ^ " not found")

let remove_from_times id times = StrMap.remove id times
    
let remove_clause_in_snd_lvl_idx p = function
| TwoLevelIndex { argno; mode; all_clauses; flex_arg_clauses; arg_idx; } ->
  TwoLevelIndex {
    argno; mode;
    all_clauses = Bl.remove p all_clauses;
    flex_arg_clauses = Bl.remove p flex_arg_clauses;
    arg_idx = Ptmap.map (Bl.remove p) arg_idx;
   }
| BitHash { mode; args; args_idx } ->
  BitHash {
    mode; args;
    args_idx = Ptmap.map (Bl.remove p) args_idx
  }
| IndexWithDiscriminationTree {mode; arg_depths; args_idx; } ->
  IndexWithDiscriminationTree {
    mode; arg_depths;
    args_idx = Discrimination_tree.remove p args_idx;
  }

let rec add1clause_compile_time ~depth { idx; time; times } ~graft predicate clause name =
  try
    let snd_lvl_idx = Ptmap.find predicate idx in
    let time = compile_time_tick time in
    match graft with
    | None ->
        let timestamp = [time] in
        let times = add_to_times clause.loc name timestamp predicate times in
        clause.timestamp <- timestamp;
        let snd_lvl_idx = add_clause_to_snd_lvl_idx ~depth ~insert:Bl.rcons predicate clause snd_lvl_idx in
        { times; time; idx = Ptmap.add predicate snd_lvl_idx idx }
    | Some (Ast.Structured.Remove x) ->
        let reference, predicate1 = time_of clause.loc x times in
        if predicate1 <> predicate then
          error ?loc:clause.loc ("cannot remove a clause for another predicate");
        let times = remove_from_times x times in
        clause.timestamp <- reference;
        let snd_lvl_idx = remove_clause_in_snd_lvl_idx (fun x -> x.timestamp = reference) snd_lvl_idx in
        { times; time; idx = Ptmap.add predicate snd_lvl_idx idx }
    | Some (Ast.Structured.Replace x) ->
        let reference, predicate1 = time_of clause.loc x times in
        if predicate1 <> predicate then
          error ?loc:clause.loc ("cannot replace a clause for another predicate");
        let times = remove_from_times x times in
        clause.timestamp <- reference;
        let snd_lvl_idx = remove_clause_in_snd_lvl_idx (fun x -> x.timestamp = reference) snd_lvl_idx in
        let snd_lvl_idx = add_clause_to_snd_lvl_idx ~depth ~insert:Bl.(insert (fun x -> lex_insertion x.timestamp reference)) predicate clause snd_lvl_idx in
        { times; time; idx = Ptmap.add predicate snd_lvl_idx idx }
    | Some (Ast.Structured.Insert gr) ->
        let timestamp =
          match gr with
          | Ast.Structured.Before x -> (fst @@ time_of clause.loc x times) @ [-time]
          | Ast.Structured.After x  -> (fst @@ time_of clause.loc x times) @ [+time] in
        let times = add_to_times clause.loc name timestamp predicate times in
        clause.timestamp <- timestamp;
        let snd_lvl_idx = add_clause_to_snd_lvl_idx ~depth ~insert:Bl.(insert (fun x -> lex_insertion x.timestamp timestamp)) predicate clause snd_lvl_idx in
        { times; time; idx = Ptmap.add predicate snd_lvl_idx idx }
  with Not_found ->
      let idx = Ptmap.add predicate (make_new_Map_snd_level_index 0 []) idx in
      add1clause_compile_time ~depth { idx; time; times } ~graft predicate clause name

let update_indexing (indexing : (Mode.hos * indexing) Constants.Map.t) (index : index) : index =
  let idx =
    C.Map.fold (fun predicate (mode, indexing) m ->
      Ptmap.add predicate 
      begin
        match indexing with
        | Hash args -> BitHash {
            args;
            mode;
            args_idx = Ptmap.empty;
          }
        | MapOn argno -> make_new_Map_snd_level_index argno mode
        | DiscriminationTree arg_depths -> IndexWithDiscriminationTree {
            arg_depths;  mode; 
            args_idx = Discrimination_tree.empty_dt arg_depths;
          }
      end m) indexing index.idx
    in
      { index with idx }

let add_to_index ~depth ~predicate ~graft clause name index : index =
  add1clause_compile_time ~depth ~graft index predicate clause name

let make_empty_index ~depth ~indexing =
  let index = update_indexing indexing { idx = Ptmap.empty; time = 0; times = StrMap.empty } in
  let index = close_index index in
  { index; src = [] }

type goal_arg_classification =
  | Variable
  | Rigid of constant

let rec classify_goal_arg ~depth t =
  match deref_head ~depth t with
  | Const k when k == Global_symbols.uvarc -> Rigid mustbevariablec
  | Const k -> Rigid(k)
  | Nil -> Rigid (Global_symbols.nilc)
  | Cons _ -> Rigid (Global_symbols.consc)
  | App (k,_,_) when k == Global_symbols.uvarc -> Rigid mustbevariablec
  | App (k,a,_) when k == Global_symbols.asc -> classify_goal_arg ~depth a
  | (App (k,_,_) | Builtin (k,_)) -> Rigid (k)
  | Lam t -> classify_goal_arg ~depth:(depth+1) t (* eta *)
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

let hash_goal_args ~depth mode args goal = match goal with
  | Const _ -> 0
  | App(k,x,xs) -> hash_goal_arg_list k ~depth (x::xs) mode args
  | _ -> assert false

let rec nth_not_found l n = match l with 
  | [] -> raise Not_found
  | x :: _ when n = 0 -> x 
  | _ :: l -> nth_not_found l (n-1)

let rec nth_not_bool_default l n = match l with 
  | [] -> Mode.Output
  | x :: _ when n = 0 -> x 
  | _ :: l -> nth_not_bool_default l (n - 1)

let trie_goal_args goal : term list = match goal with
  | Const _ -> []
  | App(_, x, xs) -> x :: xs
  | _ -> assert false

let cmp_timestamp { timestamp = tx } { timestamp = ty } = lex_insertion tx ty

let get_clauses ~depth predicate goal { index = { idx = m } } =
 let rc =
   try
     match Ptmap.find predicate m with
     | TwoLevelIndex { all_clauses; argno; mode; flex_arg_clauses; arg_idx } ->
       begin match classify_goal_argno ~depth argno goal with
       | Variable -> all_clauses
       | Rigid arg_hd ->
          try Ptmap.find arg_hd arg_idx
          with Not_found -> flex_arg_clauses
       end |> Bl.to_scan
     | BitHash { args; mode; args_idx } ->
       let hash = hash_goal_args ~depth mode args goal in
       let cl = Ptmap.find_unifiables hash args_idx |> List.map Bl.to_scan |> List.map Bl.to_list |> List.flatten in
       Bl.of_list @@ List.sort cmp_timestamp cl
     | IndexWithDiscriminationTree {arg_depths; mode; args_idx} ->
        let max_depths = Discrimination_tree.max_depths args_idx in
        let max_path = Discrimination_tree.max_path args_idx in
        let max_list_length = Discrimination_tree.max_list_length args_idx in
        let path = arg_to_trie_path ~safe:false ~depth ~is_goal:true (trie_goal_args goal) arg_depths max_depths mode max_path max_list_length in
        [%spy "dev:disc-tree:depth-path" ~rid pp_string "Goal: MaxDepths " (pplist pp_int ";") (Array.to_list max_depths)];
        [%spy "dev:disc-tree:list-size-path" ~rid pp_string "Goal: MaxListSize " pp_int max_list_length];
        (* Format.(printf "Goal: MaxDepth is %a\n" (pp_print_list ~pp_sep:(fun fmt _ -> pp_print_string fmt " ") pp_print_int) (Discrimination_tree.max_depths args_idx |> Array.to_list)); *)
        [%spy "dev:disc-tree:path" ~rid 
          Discrimination_tree.Path.pp path
          (pplist pp_int ";") arg_depths
          (*Discrimination_tree.(pp (fun fmt x -> pp_string fmt "+")) args_idx*)];
        let candidates = Discrimination_tree.retrieve cmp_timestamp path args_idx in 
          [%spy "dev:disc-tree:candidates" ~rid 
            pp_int (Bl.length candidates)];
        candidates
   with Not_found -> Bl.of_list []
 in
 [%log "get_clauses" ~rid (C.show predicate) (Bl.length rc)];
 [%spy "dev:get_clauses" ~rid C.pp predicate pp_int (Bl.length rc)];
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
   if n = 0 then t else App(Global_symbols.pic,Lam (add_pis (n-1) t),[]) in
  add_pis vars (aux t)

let local_prog { src } =  src

end (* }}} *)

open Indexing

(* Used to pass the program to the CHR runtime *)
let orig_prolog_program = Fork.new_local (make_empty_index ~depth:0 ~indexing:C.Map.empty)

(******************************************************************************
  Dynamic Prolog program
 ******************************************************************************)

module Clausify : sig

  val clausify : loc:Loc.t option -> prolog_prog -> depth:int -> term -> (constant*clause) list * clause_src list * int

  val clausify1 : loc:Loc.t -> modes:(constant -> Mode.hos) -> nargs:int -> depth:int -> term -> (constant*clause) * clause_src * int
  
  (* Utilities that deref on the fly *)
  val lp_list_to_list : depth:int -> term -> term list
  val get_lambda_body : depth:int -> term -> term
  val split_conj      : depth:int -> term -> term list

end = struct  (* {{{ *)

let rec term_map m = function
  | Const x when List.mem_assoc x m -> mkConst (List.assoc x m)
  | Const _ as x -> x
  | App(c,x,xs) when List.mem_assoc c m ->
      App(List.assoc c m,term_map m x, smart_map2 term_map m xs)
  | App(c,x,xs) -> App(c,term_map m x, smart_map2 term_map m xs)
  | Lam x -> Lam (term_map m x)
  | UVar _ as x -> x
  | AppUVar(r,lvl,xs) -> AppUVar(r,lvl,smart_map2 term_map m xs)
  | Arg _ as x -> x
  | AppArg(i,xs) -> AppArg(i,smart_map2 term_map m xs)
  | Builtin(c,xs) -> Builtin(c,smart_map2 term_map m xs)
  | Cons(hd,tl) -> Cons(term_map m hd, term_map m tl)
  | Nil as x -> x
  | Discard as x -> x
  | CData _ as x -> x

let rec split_conj ~depth = function
  | App(c, hd, args) when c == Global_symbols.andc ->
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
let rec claux1 loc get_mode vars depth hyps ts lts lcs t =
  [%trace "clausify" ~rid ("%a %d %d %d %d\n%!"
      (ppterm (depth+lts) [] ~argsdepth:0 empty_env) t depth lts lcs (List.length ts)) begin
  match t with
  | Discard -> error ?loc "ill-formed hypothetical clause: discard in head position"
  | App(c, g2, [g1]) when c == Global_symbols.rimplc ->
     claux1 loc get_mode vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == Global_symbols.rimplc -> error ?loc "ill-formed hypothetical clause"
  | App(c, g1, [g2]) when c == Global_symbols.implc ->
     claux1 loc get_mode vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == Global_symbols.implc -> error ?loc "ill-formed hypothetical clause"
  | App(c, arg, []) when c == Global_symbols.sigmac ->
     let b = get_lambda_body ~depth:(depth+lts) arg in
     let args =
      List.rev (List.filter (function (Arg _) -> true | _ -> false) ts) in
     let cst =
      match args with
         [] -> Const (depth+lcs)
       | hd::rest -> App (depth+lcs,hd,rest) in
     claux1 loc get_mode vars depth hyps (cst::ts) (lts+1) (lcs+1) b
  | App(c, arg, []) when c == Global_symbols.pic ->
     let b = get_lambda_body ~depth:(depth+lts) arg in
     claux1 loc get_mode (vars+1) depth hyps (Arg(vars,0)::ts) (lts+1) lcs b
  | App(c, _, _) when c == Global_symbols.andc ->
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
      (ppterm (depth+lcs) [] ~argsdepth:0 empty_env) g
      (pplist (ppterm (depth+lcs) [] ~argsdepth:0 empty_env) " , ")
      hyps ;*)
     let hd, args =
      match g with
         Const h -> h, []
       | App(h,x,xs) -> h, x::xs
       | UVar _ | AppUVar _
       | Arg _ | AppArg _ | Discard ->
           error ?loc "The head of a clause cannot be flexible"
       | Lam _ ->
           type_error ?loc "The head of a clause cannot be a lambda abstraction"
       | Builtin _ ->
           error ?loc "The head of a clause cannot be a builtin predicate"
       | CData _ ->
           type_error ?loc "The head of a clause cannot be a builtin data type"
       | Cons _ | Nil -> assert false
     in
     let c = { depth = depth+lcs; args; hyps; mode = get_mode hd; vars; loc; timestamp = [] } in
     [%spy "dev:claudify:extra-clause" ~rid (ppclause ~hd) c];
     (hd,c), { hdepth = depth; hsrc = g }, lcs
  | UVar ({ contents=g },from,args) when g != C.dummy ->
     claux1 loc get_mode vars depth hyps ts lts lcs
       (deref_uv ~from ~to_:(depth+lts) args g)
  | AppUVar ({contents=g},from,args) when g != C.dummy ->
     claux1 loc get_mode vars depth hyps ts lts lcs
       (deref_appuv ~from ~to_:(depth+lts) args g)
  | Arg _ | AppArg _ ->
      error ?loc "The head of a clause cannot be flexible"
  | Builtin (c,_) -> raise @@ CannotDeclareClauseForBuiltin(loc,c)
  | (Lam _ | CData _ ) as x ->
     type_error ?loc ("Assuming a string or int or float or function:" ^ show_term x)
  | UVar _ | AppUVar _ -> error ?loc "Flexible hypothetical clause"
  | Nil | Cons _ -> error ?loc "ill-formed hypothetical clause"
  end]

let clausify ~loc { index = { idx = index } } ~depth t =
  let get_mode x =
    match Ptmap.find x index with
    | TwoLevelIndex { mode } -> mode
    | BitHash { mode } -> mode
    | IndexWithDiscriminationTree { mode } -> mode
    | exception Not_found -> [] in
  let l = split_conj ~depth t in
  let clauses, program, lcs =
    List.fold_left (fun (clauses, programs, lcs) t ->
      let clause, program, lcs =
        try claux1 loc get_mode 0 depth [] [] 0 lcs t
        with CannotDeclareClauseForBuiltin(loc,c) ->
          error ?loc ("Declaring a clause for built in predicate " ^ C.show c)
      in
      clause :: clauses, program :: programs, lcs) ([],[],0) l in
  clauses, program, lcs
;;

let clausify1 ~loc ~modes ~nargs ~depth t =
  claux1 (Some loc) modes nargs depth [] [] 0 0 t

end (* }}} *)
open Clausify

(******************************************************************************
  Choice stack
 ******************************************************************************)

type goal = { depth : int; program : prolog_prog; goal : term; gid : UUID.t [@trace] }

let make_subgoal_id ogid ((depth,goal)[@trace]) =
  let gid = UUID.make () in
  [%spy "user:subgoal" ~rid ~gid: ogid UUID.pp gid];
  [%spy "user:newgoal" ~rid ~gid (uppterm depth [] ~argsdepth:0 empty_env) goal];
  gid
  [@@inline]

let make_subgoal (gid[@trace]) ~depth program goal =
  let gid[@trace] = make_subgoal_id gid ((depth,goal)[@trace]) in
   { depth ; program ; goal ; gid = gid [@trace] }
  [@@inline]

let repack_goal (gid[@trace]) ~depth program goal =
  { depth ; program ; goal ; gid = gid [@trace] }
  [@@inline]


(* The activation frames points to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. We call it catto_alts in the code. *)
type frame =
 | FNil
 | FCons of (*lvl:*)alternative * goal list * frame
and alternative = {
  cutto_alts : alternative;
  program : prolog_prog;
  adepth : int;
  agoal_hd : constant;
  ogoal_arg : term;
  ogoal_args : term list;
  agid : UUID.t; [@trace]
  goals : goal list;
  stack : frame;
  trail : T.trail;
  state : State.t;
  clauses : clause Bl.scan;
  next : alternative;
}
let noalts : alternative = Obj.magic (Sys.opaque_identity 0)

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

type runtime = {
  search : unit -> alternative;
  next_solution : alternative -> alternative;

  (* low level part *)
  destroy : unit -> unit;
  exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  get : 'a. 'a Fork.local_ref -> 'a;
}


let do_make_runtime : (?max_steps:int -> ?delay_outside_fragment:bool -> executable -> runtime) ref =
 ref (fun ?max_steps ?delay_outside_fragment _ -> anomaly "do_make_runtime not initialized")

module Constraints : sig

  type new_csts = {
    new_goals : goal list;
    some_rule_was_tried : bool; [@trace]
  }

  val propagation : unit -> new_csts
  val resumption : constraint_def list -> goal list

  val chrules : CHR.t Fork.local_ref

  (* out of place *)
  val exect_builtin_predicate :
    once:(depth:int -> term -> State.t -> State.t) ->
    constant -> depth:int -> prolog_prog -> (UUID.t[@trace]) -> term list -> term list

end = struct (* {{{ *)

type new_csts = {
  new_goals : goal list;
  some_rule_was_tried : bool; [@trace]
}

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
    from:int -> term -> env -> to_:int -> map:constant C.Map.t -> freezer -> term

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
          r @::== nt;
          t in
    let freeze_uv r =
      try List.assq r !f.uv2c
      with Not_found ->
        let n, c = C.fresh_global_constant () in
        [%spy "dev:freeze_uv:new" ~rid (fun fmt () -> let tt = UVar (r,0,0) in
          Fmt.fprintf fmt "%s == %a" (C.show n) (ppterm 0 [] ~argsdepth:0 empty_env) tt) ()];
        f := { !f with c2uv = C.Map.add n r !f.c2uv;
                       uv2c = (r,c) :: !f.uv2c };
        c in
    let rec faux d = function
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) as orig ->
          let hd' = faux d hd in
          let tl' = faux d tl in
          if hd == hd' && tl == tl' then orig
          else Cons(hd',tl')
      | App(c,x,xs) as orig ->
          let x' = faux d x in
          let xs' = smart_map (faux d) xs in
          if x == x' && xs == xs' then orig
          else App(c,x',xs')
      | Builtin(c,args) as orig ->
          let args' = smart_map (faux d) args in
          if args == args' then orig
          else Builtin(c,args')
      | (Arg _ | AppArg _) -> error "only heap terms can be frozen"
      | Lam t as orig ->
          let t' = faux (d+1) t in
          if t == t' then orig
          else Lam t'
      (* freeze *)
      | AppUVar(r,0,args) when !!r == C.dummy ->
          let args = smart_map (faux d) args in
          App(Global_symbols.uvarc, freeze_uv r, [list_to_lp_list args])
      (* expansion *)
      | UVar(r,lvl,ano) when !!r == C.dummy ->
          faux d (log_assignment(expand_uv ~depth:d r ~lvl ~ano))
      | AppUVar(r,lvl,args) when !!r == C.dummy ->
          faux d (log_assignment(expand_appuv ~depth:d r ~lvl ~args))
      (* deref *)
      | UVar(r,lvl,ano) -> faux d (deref_uv ~from:lvl ~to_:d ano !!r)
      | AppUVar(r,lvl,args) -> faux d (deref_appuv ~from:lvl ~to_:d args !!r)
    in
    [%spy "dev:freeze:in" ~rid (fun fmt () ->
      Fmt.fprintf fmt "depth:%d ground:%d newground:%d maxground:%d %a"
        depth ground newground maxground (uppterm depth [] ~argsdepth:0 empty_env) t) ()];
    let t = faux depth t in
    [%spy "dev:freeze:after-faux" ~rid (uppterm depth [] ~argsdepth:0 empty_env) t];
    let t = shift_bound_vars ~depth ~to_:ground t in
    [%spy "dev:freeze:after-shift->ground" ~rid (uppterm ground [] ~argsdepth:0 empty_env) t];
    let t = shift_bound_vars ~depth:0 ~to_:(newground-ground) t in
    [%spy "dev:freeze:after-reloc->newground" ~rid (uppterm newground [] ~argsdepth:0 empty_env) t];
    let t = shift_bound_vars ~depth:newground ~to_:maxground t in
    [%spy "dev:freeze:out" ~rid (uppterm maxground [] ~argsdepth:0 empty_env) t];
    !f, t

  let defrost ~from t env ~to_ ~map f =
  [%spy "dev:defrost:in" ~rid (fun fmt () ->
    Fmt.fprintf fmt "from:%d to:%d %a" from to_
      (uppterm from [] ~argsdepth:from env) t) ()];
    let t = full_deref ~adepth:from env ~depth:from t in
  [%spy "dev:defrost:fully-derefd" ~rid (fun fmt ()->
    Fmt.fprintf fmt "from:%d to:%d %a" from to_
      (uppterm from [] ~argsdepth:0 empty_env) t) ()];
    let t = map_free_vars ~map ~depth:from ~to_ t in
  [%spy "dev:defrost:shifted" ~rid (fun fmt () ->
    Fmt.fprintf fmt "from:%d to:%d %a" from to_
      (uppterm to_ [] ~argsdepth:0 empty_env) t) ()];
    let rec daux d = function
      | Const c when C.Map.mem c f.c2uv ->
          UVar(C.Map.find c f.c2uv,0,0)
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) as orig ->
          let hd' = daux d hd in
          let tl' = daux d tl in
          if hd == hd' && tl == tl' then orig
          else Cons(hd',tl')
      | App(c,UVar(r,lvl,ano),a) when !!r != C.dummy ->
          daux d (App(c,deref_uv ~to_:d ~from:lvl ano !!r,a))
      | App(c,AppUVar(r,lvl,args),a) when !!r != C.dummy ->
          daux d (App(c,deref_appuv ~to_:d ~from:lvl args !!r,a))
      | App(c,Const x,[args]) when c == Global_symbols.uvarc ->
          let r = C.Map.find x f.c2uv in
          let args = lp_list_to_list ~depth:d args in
          mkAppUVar r 0 (smart_map (daux d) args)
      | App(c,UVar(r,_,_),[args]) when c == Global_symbols.uvarc ->
          let args = lp_list_to_list ~depth:d args in
          mkAppUVar r 0 (smart_map (daux d) args)
      | App(c,AppUVar(r,_,_),[args]) when c == Global_symbols.uvarc ->
          let args = lp_list_to_list ~depth:d args in
          mkAppUVar r 0 (smart_map (daux d) args)
      | App(c,x,xs) as orig ->
          let x' = daux d x in
          let xs' = smart_map (daux d) xs in
          if x == x' && xs == xs' then orig
          else App(c,x', xs')
      | Builtin(c,args) as orig ->
          let args' = smart_map (daux d) args in
          if args == args' then orig
          else Builtin(c,args')
      | Arg(i,ano) when env.(i) != C.dummy ->
          daux d (deref_uv ~from:to_ ~to_:d ano env.(i))
      | AppArg (i,args) when env.(i) != C.dummy ->
          daux d (deref_appuv ~from:to_ ~to_:d args env.(i))
      | (Arg(i,_) | AppArg(i,_)) as x ->
          env.(i) <- UVar(oref C.dummy, to_, 0);
          daux d x
      | Lam t as orig ->
          let t' = daux (d+1) t in
          if t == t' then orig
          else Lam t'
      | UVar _ as x -> x
      | AppUVar(r,lvl,args) as orig ->
          let args' = smart_map (daux d) args in
          if args == args' then orig
          else AppUVar(r,lvl,args')
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
  [%spy "dev:replace_const:in" ~rid (uppterm 0 [] ~argsdepth:0 empty_env) t];
  let t = rcaux t in
  [%spy "dev:replace_const:out" ~rid (uppterm 0 [] ~argsdepth:0 empty_env) t];
  t
;;
let ppmap fmt (g,l) =
  let aux fmt (c1,c2) = Fmt.fprintf fmt "%s -> %s" (C.show c1) (C.show c2) in
  Fmt.fprintf fmt "%d = %a" g (pplist aux ",") l
;;


end (* }}} *)

let match_goal (gid[@trace]) goalno maxground env freezer (newground,depth,t) pattern =
  let freezer, t =
    Ice.freeze ~depth t ~ground:depth ~newground ~maxground freezer in
  [%trace "match_goal" ~rid ("@[<hov>%a ===@ %a@]"
     (uppterm maxground [] ~argsdepth:maxground env) t
     (uppterm 0 [] ~argsdepth:maxground env) pattern) begin
  if unif ~argsdepth:maxground ~matching:false (gid[@trace]) maxground env 0 t pattern then freezer
  else raise NoMatch
  end]

let match_context (gid[@trace]) goalno maxground env freezer (newground,ground,lt) pattern =
  if pattern == Discard then freezer else
  let freezer, lt =
    map_acc (fun freezer { hdepth = depth; hsrc = t } ->
      Ice.freeze ~depth t ~ground ~newground ~maxground freezer)
    freezer lt in
  let t = list_to_lp_list lt in
  [%trace "match_context" ~rid ("@[<hov>%a ===@ %a@]"
     (uppterm maxground [] ~argsdepth:maxground env) t
     (uppterm 0 [] ~argsdepth:maxground env) pattern) begin
  if unif ~argsdepth:maxground ~matching:false (gid[@trace]) maxground env 0 t pattern then freezer
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

let make_constraint_def ~rid ~gid:(gid[@trace]) depth prog pdiff conclusion =
  { cdepth = depth; prog = prog; context = pdiff; cgid = gid [@trace]; conclusion }

let delay_goal ?(filter_ctx=fun _ -> true) ~depth prog ~goal:g (gid[@trace]) ~on:keys =
  let pdiff = local_prog prog in
  let pdiff = List.filter filter_ctx pdiff in
  let gid[@trace] = make_subgoal_id gid (depth,g) in
  let kind = Constraint (make_constraint_def ~rid ~gid:(gid[@trace]) depth prog pdiff g) in
  CS.declare_new { kind ; blockers = keys }
;;

let rec head_of = function
  | Const x -> x
  | App(x,Lam f,_) when x == Global_symbols.pic -> head_of f
  | App(x,hd,_) when x == Global_symbols.rimplc -> head_of hd
  | App(x,hd,_) when x == Global_symbols.andc -> head_of hd (* FIXME *)
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

let declare_constraint ~depth prog (gid[@trace]) args =
  let g, keys =
    match args with
    | t1 :: more ->
      let err =
        "the Key arguments of declare_constraint must be variables or list of variables"
      in
      let rec collect_keys t = match deref_head ~depth t with
        | UVar (r, _, _) | AppUVar (r, _, _) -> [r]
        | Discard -> [dummy_uvar_body]
        | Lam _ ->
            begin match HO.eta_contract_flex ~depth t with
            | None -> type_error err
            | Some t -> collect_keys t
            end
        | _ -> type_error err
      and collect_keys_list t = match deref_head ~depth t with
        | Nil -> []
        | Cons(hd,tl) -> collect_keys hd @ collect_keys_list tl
        | x -> collect_keys x
      in
        t1, List.flatten (List.map collect_keys_list more)
    | _ -> type_error "declare_constraint takes at least one argument"
  in 
  match CHR.clique_of (head_of g) !chrules with
  | Some (clique, ctx_filter) -> (* real constraint *)
     (* XXX head_of is weak because no clausify ? XXX *)
     delay_goal ~filter_ctx:(fun { hsrc = x } -> 
        C.Set.mem (head_of x) clique || C.Set.mem (head_of x) ctx_filter)
       ~depth prog ~goal:g (gid[@trace]) ~on:keys
  | None -> delay_goal ~depth prog ~goal:g (gid[@trace]) ~on:keys

let exect_builtin_predicate ~once c ~depth idx (gid[@trace]) args =
       if c == Global_symbols.declare_constraintc then begin
               declare_constraint ~depth idx (gid[@trace]) args; [] end
  else if c == Global_symbols.print_constraintsc then begin
               printf "@[<hov 0>%a@]\n%!" (CS.print ?pp_ctx:None) (CS.contents ());
               [] 
  end else
    let b =
      try FFI.lookup c
      with Not_found -> 
        anomaly ("no built-in predicated named " ^ C.show c) in
    let constraints = !CS.Ugly.delayed in
    let state = !CS.state  in
    let state, gs = FFI.call b ~once ~depth (local_prog idx) constraints state args in
    let state, gs = State.get Data.Conversion.extra_goals_postprocessing state gs state in
    CS.state := state;
    List.map Data.Conversion.term_of_extra_goal gs
;;

let match_head { conclusion = x; cdepth } p =
  match deref_head ~depth:cdepth x with
  | Const x -> x == p
  | App(x,_,_) -> x == p
  | _ -> false
;;

let pp_opt start f fmt = function
  | None -> ()
  | Some x -> Fmt.fprintf fmt "%s%a" start f x

let pp_optl start f fmt = function
  | [] -> ()
  | x -> Fmt.fprintf fmt "%s%a" start (pplist f " ") x

let pp_optterm stop fmt x =
  match deref_head ~depth:0 x with
  | Discard -> ()
  | _ -> Fmt.fprintf fmt "%a%s" (uppterm 0 [] ~argsdepth:0 empty_env) x stop

let pp_sequent fmt { CHR.eigen; context; conclusion } =
  Fmt.fprintf fmt "@[<hov 2>(%a%a%a)@]"
    (pp_optterm " : ") eigen
    (pp_optterm " ?- ") context
    (uppterm 0 [] ~argsdepth:0 empty_env) conclusion

let pp_urule fmt { CHR. to_match; to_remove; new_goal; guard } =
  Fmt.fprintf fmt "@[<hov 2>%a@ %a@ %a@ %a@]"
    (pplist pp_sequent " ") to_match
    (pp_optl "\\ " pp_sequent) to_remove
    (pp_opt "| " (uppterm ~min_prec:Elpi_parser.Parser_config.inf_precedence 0 [] ~argsdepth:0 empty_env)) guard
    (pp_opt "<=> " pp_sequent) new_goal


let try_fire_rule (gid[@trace]) rule (constraints as orig_constraints) =

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
    match_goal (gid[@trace]) i max_depth env m (dto,d,list_to_lp_list @@ C.mkinterval 0 eigen 0) pat in
  let match_conclusion i m g pat =
    match_goal (gid[@trace]) i max_depth env m g pat in
  let match_context i m ctx pctx =
    match_context (gid[@trace]) i max_depth env m ctx pctx in

  let guard =
    match guard with
    | Some g -> g
    | None -> mkConst Global_symbols.truec
  in
 
  let initial_program = !orig_prolog_program in
 
  let executable = {
    (* same program *)
    compiled_program = initial_program; 
    (* no meta meta level *)
    chr = CHR.empty;
    initial_goal =
      (* TODO: maybe we don't need to do this if we don't reach the guard *)
      move ~argsdepth:max_depth ~from:max_depth ~to_:max_depth env
        (shift_bound_vars ~depth:0 ~to_:max_depth guard);
    assignments = StrMap.empty;
    initial_depth = max_depth;
    initial_runtime_state = !CS.initial_state;
    symbol_table = !C.table;
    builtins = !FFI.builtins;
  } in
  let { search; get; exec; destroy } = !do_make_runtime executable in
 
  let check_guard () =
    try
      let _ = search () in
      if get CS.Ugly.delayed <> [] then
        error "propagation rules must not declare constraint(s)"
    with No_clause -> raise NoMatch in

  let result = try

    (* matching *)
    let m = exec (fun m ->
      [%spy "dev:CHR:candidate" ~rid
        (pplist (fun f x ->
           let dto,dt,t = x in
           Format.fprintf f "(lives-at:%d, to-be-lifted-to:%d) %a"
             dt dto (uppterm dt [] ~argsdepth:0 empty_env) t) ";") constraints_goals];

      let m = fold_left2i match_conclusion m
        constraints_goals patterns_goals in
      let m = fold_left2i match_context m
        constraints_contexts patterns_contexts in
      let m = fold_left2i match_eigen m
        constraints_depts patterns_eigens in

      [%spy "dev:CHR:matching-assignments" ~rid
        (pplist (uppterm max_depth [] ~argsdepth:0 empty_env) ~boxed:false ",") (Array.to_list env)];

      T.to_resume := [];
      assert(!T.new_delayed = []);
      m) Ice.empty_freezer in

    [%spy "dev:CHR:maxdepth" ~rid Fmt.pp_print_int max_depth];

    check_guard ();

    (* result *)
    let _, constraints_to_remove =
      let len_pats_to_match = List.length pats_to_match in
      partition_i (fun i _ -> i < len_pats_to_match) orig_constraints in
    let new_goals =
      match new_goal with
      | None -> None
      | Some { CHR.eigen; context; conclusion } ->
      let eigen =
        match full_deref ~adepth:max_depth env ~depth:max_depth eigen with
        | (Nil | Cons _) as x -> lp_list_to_list ~depth:max_depth x
        | Discard -> C.mkinterval 0 max_depth 0
        | _ -> error "eigen not resolving to a list of names" 
      in
      let max_eigen,map = List.fold_left (fun (i,m) c ->
          i+1,C.Map.add (Data.destConst c) i m)
        (0,C.Map.empty) eigen in
      let conclusion =
        Ice.defrost ~from:max_depth ~to_:max_eigen ~map
          (App(Global_symbols.implc,context,[conclusion])) env m in
      (* TODO: check things make sense in heigen *)
      let prog = initial_program in
      Some (make_constraint_def ~rid ~gid:((make_subgoal_id gid (max_eigen,conclusion))[@trace]) max_eigen prog [] conclusion) in
    [%spy "dev:CHR:try-rule:success" ~rid];
    Some(rule_name, constraints_to_remove, new_goals, Ice.assignments m)
  with NoMatch ->
    [%spy "dev:CHR:try-rule:fail" ~rid];
    None
  in
  destroy ();
  result
;;

let resumption to_be_resumed_rev =
  List.map (fun { cdepth = d; prog; conclusion = g; cgid = gid [@trace] } ->
    (repack_goal[@inlined]) ~depth:d (gid[@trace]) prog g)
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
  let some_rule_fired[@trace] = ref false in
  let some_rule_was_tried[@trace] = ref false in
  let orig_store_contents[@trace] = CS.contents () in
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
             else begin
               let ()[@trace] = some_rule_was_tried := true in
               [%spy "user:CHR:try" ~rid ~gid:active.cgid Loc.pp rule.rule_loc pp_urule rule];
               match try_fire_rule (active.cgid[@trace]) rule constraints with
               | None -> [%spy "user:CHR:rule-failed" ~rid ]
               | Some (rule_name, to_be_removed, to_be_added, assignments) ->
                   let ()[@trace] = some_rule_fired := true in
                   [%spy "user:CHR:rule-fired" ~rid ~gid: (active.cgid[@trace]) pp_string rule_name];
                   [%spyl "user:CHR:rule-remove-constraints" ~rid ~gid: (active.cgid[@trace]) (fun fmt { cgid } -> UUID.pp fmt cgid) to_be_removed];
                   removed := to_be_removed @ !removed;
                   List.iter CS.remove_old_constraint to_be_removed;
                   List.iter (fun (r,_lvl,t) -> r @:= t) assignments;
                   match to_be_added with
                   | None -> ()
                   | Some to_be_added -> to_be_resumed_rev := to_be_added :: !to_be_resumed_rev
            end)
         done);
  done;
  let ()[@trace] =
    if !some_rule_fired then begin
      orig_store_contents |> List.iter (fun it ->
        [%spy "user:CHR:store:before" ~rid CS.print_gid it CS.print1 it]
        );
      CS.contents () |> List.iter (fun it ->
        [%spy "user:CHR:store:after" ~rid CS.print_gid it CS.print1 it]
        );
      end;
  in
  { new_goals = resumption !to_be_resumed_rev;
    some_rule_was_tried = !some_rule_was_tried [@trace] }

end (* }}} *)

(******************************************************************************
  Main loop = SLD + delay/resumption
 ******************************************************************************)

module Mainloop : sig

  val make_runtime : ?max_steps:int -> ?delay_outside_fragment:bool -> executable -> runtime

end = struct (* {{{ *)

let steps_bound = Fork.new_local None
let steps_made = Fork.new_local 0

let pred_of g =
  match g with
  | App(c,_,_) -> Some(C.show c)
  | Const c -> Some(C.show c)
  | Builtin(c,_) -> Some(C.show c)
  | _ -> None

let pp_candidate ~depth ~k fmt ({ loc } as cl) =
  match loc with
  | Some x -> Util.CData.pp fmt (Ast.cloc.Util.CData.cin x)
  | None -> Fmt.fprintf fmt "hypothetical clause: %a" (ppclause ~hd:k) cl

let hd_c_of = function
  | Const _ as x -> x
  | App(x,_,_) -> C.mkConst x
  | Builtin(x,_) -> C.mkConst x
  | _ -> C.dummy

let pp_resumed_goal { depth; program; goal; gid = gid[@trace] } =
  [%spy "user:rule:resume:resumed" ~rid ~gid (uppterm depth [] ~argsdepth:0 empty_env) goal]
;;
let pp_CHR_resumed_goal { depth; program; goal; gid = gid[@trace] } =
  [%spy "user:CHR:resumed" ~rid ~gid (uppterm depth [] ~argsdepth:0 empty_env) goal]
;;


(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ?max_steps: int -> ?delay_outside_fragment: bool -> executable -> runtime =
  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     depth >= 0 is the number of variables in the context. *)
  let rec run depth p g (gid[@trace]) gs (next : frame) alts cutto_alts =
    [%cur_pred (pred_of g)];
    [%trace "run" ~rid begin

    begin match !steps_bound with
    | Some bound ->
        incr steps_made; if !steps_made > bound then raise No_more_steps
    | None -> ()
    end;

 match resume_all () with
 | None ->
    [%tcall next_alt alts]
 | Some ({ depth = ndepth; program; goal; gid = ngid [@trace] } :: goals) ->
    [%tcall run ndepth program goal (ngid[@trace]) (goals @ (repack_goal[@inlined]) (gid[@trace]) ~depth p g :: gs) next alts cutto_alts]
 | Some [] ->
    [%spyl "user:curgoal" ~rid ~gid (uppterm depth [] ~argsdepth:0 empty_env) [hd_c_of g;g]];
    match g with
    | Builtin(c,[]) when c == Global_symbols.cutc ->
       [%tcall cut (gid[@trace]) gs next (alts[@trace]) cutto_alts]
    | Builtin(c,[q;sol]) when c == Global_symbols.findall_solutionsc ->
       [%tcall findall depth p q sol (gid[@trace]) gs next alts cutto_alts]
    | App(c, g, gs') when c == Global_symbols.andc -> [%spy "user:rule" ~rid ~gid pp_string "and"];
       let gid'[@trace] = make_subgoal_id gid ((depth,g)[@trace]) in
       let gs' = List.map (fun x -> (make_subgoal[@inlined]) ~depth (gid[@trace]) p x) gs' in
       [%spy "user:rule:and" ~rid ~gid pp_string "success"];
       [%tcall run depth p g (gid'[@trace]) (gs' @ gs) next alts cutto_alts]
    | Cons (g,gs') -> [%spy "user:rule" ~rid ~gid pp_string "and"];
       let gid'[@trace] = make_subgoal_id gid ((depth,g)[@trace]) in
       let gs' = (make_subgoal[@inlined]) ~depth (gid[@trace]) p gs' in
       [%spy "user:rule:and" ~rid ~gid pp_string "success"];
       [%tcall run depth p g (gid'[@trace]) (gs' :: gs) next alts cutto_alts]
    | Nil -> [%spy "user:rule" ~rid ~gid pp_string "true"]; [%spy "user:rule:true" ~rid ~gid pp_string "success"];
      begin match gs with
      | [] -> [%tcall pop_andl alts next cutto_alts]
      | { depth; program; goal; gid = gid [@trace] } :: gs ->
        [%tcall run depth program goal (gid[@trace]) gs next alts cutto_alts]
      end
    | Builtin(c,[l;r]) when c == Global_symbols.eqc -> [%spy "user:rule" ~rid ~gid pp_string "eq"]; [%spy "user:rule:builtin:name" ~rid ~gid pp_string (C.show c)];
       if unif ~argsdepth:depth ~matching:false (gid[@trace]) depth empty_env depth l r then begin
         [%spy "user:rule:eq" ~rid ~gid pp_string "success"];
         match gs with
         | [] -> [%tcall pop_andl alts next cutto_alts]
         | { depth; program; goal; gid = gid [@trace] } :: gs ->
           [%tcall run depth program goal (gid[@trace]) gs next alts cutto_alts]
       end else begin
         [%spy "user:rule:eq" ~rid ~gid pp_string "fail"];
         [%tcall next_alt alts]
       end
    | App(c, g2, [g1]) when c == Global_symbols.rimplc -> [%spy "user:rule" ~rid ~gid pp_string "implication"];
       let [@warning "-26"]loc = None in
       let loc[@trace] = Some (Loc.initial ("(context step_id:" ^ string_of_int (Trace_ppx_runtime.Runtime.get_cur_step ~runtime_id:!rid "run") ^")")) in
       let clauses, pdiff, lcs = clausify ~loc p ~depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       let gid[@trace] = make_subgoal_id gid ((depth,g2)[@trace]) in
       [%spy "user:rule:implication" ~rid ~gid pp_string "success"];
       [%tcall run (depth+lcs) (add_clauses ~depth clauses pdiff p) g2 (gid[@trace]) gs next alts cutto_alts]
    | App(c, g1, [g2]) when c == Global_symbols.implc -> [%spy "user:rule" ~rid ~gid pp_string "implication"];
       let [@warning "-26"]loc = None in
       let loc[@trace] = Some (Loc.initial ("(context step_id:" ^ string_of_int (Trace_ppx_runtime.Runtime.get_cur_step ~runtime_id:!rid "run") ^")")) in
       let clauses, pdiff, lcs = clausify ~loc p ~depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       let gid[@trace] = make_subgoal_id gid ((depth,g2)[@trace]) in
       [%spy "user:rule:implication" ~rid ~gid pp_string "success"];
       [%tcall run (depth+lcs) (add_clauses ~depth clauses pdiff p) g2 (gid[@trace]) gs next alts cutto_alts]
    | App(c, arg, []) when c == Global_symbols.pic -> [%spy "user:rule" ~rid ~gid pp_string "pi"];
       let f = get_lambda_body ~depth arg in
       let gid[@trace] = make_subgoal_id gid ((depth+1,f)[@trace]) in
       [%spy "user:rule:pi" ~rid ~gid pp_string "success"];
       [%tcall run (depth+1) p f (gid[@trace]) gs next alts cutto_alts]
    | App(c, arg, []) when c == Global_symbols.sigmac -> [%spy "user:rule" ~rid ~gid pp_string "sigma"];
       let f = get_lambda_body ~depth arg in
       let v = UVar(oref C.dummy, depth, 0) in
       let fv = subst depth [v] f in
       let gid[@trace] = make_subgoal_id gid ((depth,fv)[@trace]) in
       [%spy "user:rule:sigma" ~rid ~gid pp_string "success"];
       [%tcall run depth p fv (gid[@trace]) gs next alts cutto_alts]
    | UVar ({ contents = g }, from, args) when g != C.dummy -> [%spy "user:rule" ~rid ~gid pp_string "deref"]; [%spy "user:rule:deref" ~rid ~gid pp_string "success"];
       [%tcall run depth p (deref_uv ~from ~to_:depth args g) (gid[@trace]) gs next alts cutto_alts]
    | AppUVar ({contents = t}, from, args) when t != C.dummy -> [%spy "user:rule" ~rid ~gid pp_string "deref"]; [%spy "user:rule:deref" ~rid ~gid pp_string "success"];
       [%tcall run depth p (deref_appuv ~from ~to_:depth args t) (gid[@trace]) gs next alts cutto_alts]
    | Const k ->
       let clauses = get_clauses ~depth k g p in
       [%spy "user:rule" ~rid ~gid pp_string "backchain"];
       [%spyl "user:rule:backchain:candidates" ~rid ~gid (pp_candidate ~depth ~k) (Bl.to_list clauses)];
       [%tcall backchain depth p (k, C.dummy, [], gs) (gid[@trace]) next alts cutto_alts clauses]
    | App (k,x,xs) ->
       let clauses = get_clauses ~depth k g p in
       [%spy "user:rule" ~rid ~gid pp_string "backchain"];
       [%spyl "user:rule:backchain:candidates" ~rid ~gid (pp_candidate ~depth ~k) (Bl.to_list clauses)];
       [%tcall backchain depth p (k, x, xs, gs) (gid[@trace]) next alts cutto_alts clauses]
    | Builtin(c, args) -> [%spy "user:rule" ~rid ~gid pp_string "builtin"]; [%spy "user:rule:builtin:name" ~rid ~gid pp_string (C.show c)];
       let once ~depth g state =
         CS.state := state;
         let { depth; program; goal; gid = gid [@trace] } = (make_subgoal[@inlined]) (gid[@trace]) ~depth p g in
           let _alts = run depth program goal (gid[@trace]) [] FNil noalts noalts in
           !CS.state in
       begin match Constraints.exect_builtin_predicate ~once c ~depth p (gid[@trace]) args with
       | gs' ->
          [%spy "user:rule:builtin" ~rid ~gid pp_string "success"];
          (match List.map (fun g -> (make_subgoal[@inlined]) (gid[@trace]) ~depth p g) gs' @ gs with
          | [] -> [%tcall pop_andl alts next cutto_alts]
          | { depth; program; goal; gid = gid [@trace] } :: gs -> [%tcall run depth program goal (gid[@trace]) gs next alts cutto_alts])
       | exception No_clause ->
          [%spy "user:rule:builtin" ~rid ~gid pp_string "fail"];
          [%tcall next_alt alts]
       end
    | Arg _ | AppArg _ -> anomaly "The goal is not a heap term"
    | Lam _ | CData _ ->
        type_error ("The goal is not a predicate:" ^ (show_term g))
    | UVar _ | AppUVar _ | Discard ->
        error "The goal is a flexible term"
  end]

  (* We pack some arguments into a tuple otherwise we consume too much stack *)
  and backchain depth p (k, arg, args_of_g, gs) (gid[@trace]) next alts cutto_alts cp = [%trace "select" ~rid begin
    if Bl.is_empty cp then begin
        [%spy "user:rule:backchain" ~rid ~gid pp_string "fail"];
        [%tcall next_alt alts]
    end else
      let { depth = c_depth; mode = c_mode; args = c_args; hyps = c_hyps; vars = c_vars; loc }, cs = Bl.next cp in
        [%spy "user:rule:backchain:try" ~rid ~gid (pp_option Util.CData.pp) (Util.option_map Ast.cloc.Util.CData.cin loc) (ppclause ~hd:k) { depth = c_depth; mode = c_mode; args = c_args; hyps = c_hyps; vars = c_vars; loc; timestamp = [] }];
        let old_trail = !T.trail in
        T.last_call := alts == noalts && Bl.is_empty cs;
        let env = Array.make c_vars C.dummy in
        match
          match c_args with
          | [] -> arg == C.dummy && args_of_g == []
          | x :: xs -> arg != C.dummy &&
             match c_mode with
             | [] -> unif ~argsdepth:depth ~matching:false (gid[@trace]) depth env c_depth arg x && for_all23 ~argsdepth:depth (unif (gid[@trace])) depth env c_depth args_of_g xs
             | arg_mode :: ms -> unif ~argsdepth:depth ~matching:(Mode.get_head arg_mode == Input) (gid[@trace]) depth env c_depth arg x && for_all3b3 ~argsdepth:depth (unif (gid[@trace])) depth env c_depth args_of_g xs ms false
        with
        | false ->
            T.undo ~old_trail (); [%tcall backchain depth p (k, arg, args_of_g, gs) (gid[@trace]) next alts cutto_alts cs]
        | true ->
           let oldalts = alts in
           let alts = if Bl.is_empty cs then alts else
             { program = p; adepth = depth; agoal_hd = k; ogoal_arg = arg; ogoal_args = args_of_g; agid = gid[@trace]; goals = gs; stack = next;
               trail = old_trail;
               state = !CS.state;
               clauses = cs; cutto_alts = cutto_alts ; next = alts} in
           begin match c_hyps with
           | [] ->
              [%spy "user:rule:backchain" ~rid ~gid pp_string "success"];
              begin match gs with
              | [] -> [%tcall pop_andl alts next cutto_alts]
              | { depth ; program; goal; gid = gid [@trace] } :: gs -> [%tcall run depth program goal (gid[@trace]) gs next alts cutto_alts] end
           | h::hs ->
              let next = if gs = [] then next else FCons (cutto_alts,gs,next) in
              let h = move ~argsdepth:depth ~from:c_depth ~to_:depth env h in
              let gid[@trace] = make_subgoal_id gid ((depth,h)[@trace]) in
              let hs =
                List.map (fun x->
                  (make_subgoal[@inlined]) (gid[@trace]) ~depth p (move ~argsdepth:depth ~from:c_depth ~to_:depth env x))
                  hs in
              [%spy "user:rule:backchain" ~rid ~gid pp_string "success"];
              [%tcall run depth p h (gid[@trace]) hs next alts oldalts] end
    end]

  and cut (gid[@trace]) gs next (alts[@trace]) cutto_alts =
    [%spy "user:rule" ~rid ~gid pp_string "cut"];
    let ()[@trace] =
      let rec prune ({ agid = agid[@trace]; clauses; adepth = depth; agoal_hd = hd } as alts) =
        if alts != cutto_alts then begin
          List.iter (fun c -> 
            [%spy "user:rule:cut:branch" ~rid UUID.pp agid (pp_option Util.CData.pp) (Util.option_map Ast.cloc.Util.CData.cin c.loc) (ppclause ~hd) c])
          (clauses |> Bl.to_list);
          prune alts.next
        end
      in
        prune alts in
    if cutto_alts == noalts then (T.cut_trail[@inlined]) ();
    [%spy "user:rule:cut" ~rid ~gid pp_string "success"];
    match gs with
    | [] -> pop_andl cutto_alts next cutto_alts
    | { depth; program; goal; gid = gid [@trace] } :: gs -> run depth program goal (gid[@trace]) gs next cutto_alts cutto_alts

  and findall depth p g s (gid[@trace]) gs next alts cutto_alts =
    [%spy "user:rule" ~rid ~gid pp_string "findall"];
    let avoid = oref C.dummy in (* to force a copy *)
    let copy = move ~argsdepth:depth ~from:depth ~to_:depth empty_env ~avoid in
    let g = copy g in (* so that Discard becomes a variable *)
    [%trace "findall" ~rid ("@[<hov 2>query: %a@]" (uppterm depth [] ~argsdepth:0 empty_env) g) begin
    let executable = {
      (* same program *)
      compiled_program = p; 
      (* no meta meta level *)
      chr = CHR.empty;
      initial_goal = g;
      assignments = StrMap.empty;
      initial_depth = depth;
      initial_runtime_state = !CS.initial_state;
      symbol_table = !C.table;
      builtins = !FFI.builtins;
    } in
    let { search; next_solution; destroy; get; _ } = !do_make_runtime executable in
    let solutions = ref [] in
    let add_sol () =
      if get CS.Ugly.delayed <> [] then
        error "findall search must not declare constraint(s)";
      let sol = copy g in
      [%spy "findall solution:" ~rid ~gid (ppterm depth [] ~argsdepth:0 empty_env) g];
      solutions := sol :: !solutions in
    let alternatives = ref noalts in
    try
      alternatives := search ();
      add_sol ();
      while true do
        alternatives := next_solution !alternatives;
        add_sol ();
      done;
      raise No_clause
    with No_clause ->
      destroy ();
      let solutions = list_to_lp_list (List.rev !solutions) in
      [%spy "findall solutions:" ~rid ~gid (ppterm depth [] ~argsdepth:0 empty_env) solutions];
      match unif ~argsdepth:depth ~matching:false (gid[@trace]) depth empty_env depth s solutions with
      | false ->
        [%spy "user:rule:findall" ~rid ~gid pp_string "fail"];
        [%tcall next_alt alts]
      | true ->
        [%spy "user:rule:findall" ~rid ~gid pp_string "success"];
        begin match gs with
        | [] -> [%tcall pop_andl alts next cutto_alts]
        | { depth ; program; goal; gid = gid [@trace] } :: gs -> [%tcall run depth program goal (gid[@trace]) gs next alts cutto_alts] end
    end]

  and pop_andl alts next cutto_alts =
   match next with
    | FNil ->
        (match resume_all () with
           None ->
            Fmt.fprintf Fmt.std_formatter
             "Undo triggered by goal resumption\n%!";
            [%tcall next_alt alts]
         | Some ({ depth; program; goal; gid = gid [@trace] } :: gs) ->
            run depth program goal (gid[@trace]) gs FNil alts cutto_alts
         | Some [] -> alts)
    | FCons (_,[],_) -> anomaly "empty stack frame"
    | FCons(cutto_alts, { depth; program; goal; gid = gid [@trace] } :: gs, next) ->
        run depth program goal (gid[@trace]) gs next alts cutto_alts

  and resume_all () : goal list option =
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
         [%spy "user:resume-unif" ~rid (fun fmt () -> Fmt.fprintf fmt
           "@[<hov 2>^%d:%a@ == ^%d:%a@]\n%!"
           adepth (uppterm adepth [] ~argsdepth:0 empty_env) a
           bdepth (uppterm bdepth [] ~argsdepth:adepth env) b) ()];
         ok := unif ~argsdepth:adepth ~matching ((UUID.make ())[@trace]) adepth env bdepth a b
     | { kind = Constraint dpg } as c :: rest ->
         CS.remove_old c;
         CS.to_resume := rest;
         (*Fmt.fprintf Fmt.std_formatter
          "Resuming goal: @[<hov 2> ...@ ⊢^%d %a@]\n%!"
          (*"Resuming goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
          (*(pplist (uppterm depth [] ~argsdepth:0 empty_env) ",") pdiff*)
          depth (uppterm depth [] ~argsdepth:0 empty_env) g ;*)
         to_be_resumed := dpg :: !to_be_resumed
     | _ -> anomaly "Unknown constraint type"
   done ;
   (* Phase 2: we propagate the constraints *)
   if !ok then
     let to_be_resumed = Constraints.resumption !to_be_resumed in

     let ()[@trace] =
       if to_be_resumed != [] then begin
        [%spy "user:rule" ~rid pp_string "resume"];
        List.iter pp_resumed_goal to_be_resumed;
        [%spy "user:rule:resume" ~rid pp_string "success"];
       end in

     (* Optimization: check here new_delayed *)
     if !CS.new_delayed <> [] then begin

      let ()[@trace] =
        if to_be_resumed != [] then begin
          Trace_ppx_runtime.Runtime.incr_cur_step ~runtime_id:!rid "run";
        end in

      let { Constraints.new_goals;
            some_rule_was_tried = some_rule_was_tried[@trace] } =
        Constraints.propagation () in

      let ()[@trace] =
        List.iter pp_CHR_resumed_goal new_goals;
        if some_rule_was_tried && new_goals = [] then begin
          Trace_ppx_runtime.Runtime.incr_cur_step ~runtime_id:!rid "run";
        end in
  
      Some (to_be_resumed @ new_goals)
     end else
      Some to_be_resumed
   else begin
    [%spy "user:rule" ~rid pp_string "constraint-failure"];
    None
   end

  and next_alt alts =
   if alts == noalts then raise No_clause
   else
     let { program = p; clauses; agoal_hd = k; ogoal_arg = arg; ogoal_args = args; agid = gid [@trace]; goals = gs; stack = next;
          trail = old_trail; state = old_state;
          adepth = depth; cutto_alts = cutto_alts; next = alts} = alts in
    T.undo ~old_trail ~old_state ();

    [%trace "run" ~rid begin
    [%cur_pred (Some (C.show k))];
    [%spyl "user:curgoal" ~rid ~gid (uppterm depth [] ~argsdepth:0 empty_env) [Const k;App(k,arg,args)]];
    [%spy "user:rule" ~rid ~gid pp_string "backchain"];
    [%spyl "user:rule:backchain:candidates" ~rid ~gid (pp_candidate ~depth ~k) (Bl.to_list clauses)];
    [%tcall backchain depth p (k, arg, args, gs) (gid[@trace]) next alts cutto_alts clauses]
    end]
  in

 (* Finally the runtime *)
 fun ?max_steps ?(delay_outside_fragment = false) {
    compiled_program;
    chr;
    initial_depth;
    initial_goal;
    initial_runtime_state;
    assignments;
    symbol_table;
    builtins;
  } ->
  let { Fork.exec = exec ; get = get ; set = set } = Fork.fork () in
  set orig_prolog_program compiled_program;
  set Constraints.chrules chr;
  set T.initial_trail T.empty;
  set T.trail T.empty;
  set T.last_call false;
  set CS.new_delayed [];
  set CS.to_resume [];
  set CS.blockers_map IntMap.empty;
  set CS.Ugly.delayed [];
  set steps_bound max_steps;
  set delay_hard_unif_problems delay_outside_fragment;
  set steps_made 0;
  set CS.state initial_runtime_state;
  set CS.initial_state initial_runtime_state;
  set C.table symbol_table;
  set FFI.builtins builtins;
  set rid !max_runtime_id;
  let search = exec (fun () ->
     [%spy "dev:trail:init" ~rid (fun fmt () -> T.print_trail fmt) ()];
     let gid[@trace] = UUID.make () in
     [%spy "user:newgoal" ~rid ~gid (uppterm initial_depth [] ~argsdepth:0 empty_env) initial_goal];
     T.initial_trail := !T.trail;
     run initial_depth !orig_prolog_program initial_goal (gid[@trace]) [] FNil noalts noalts) in
  let destroy () = exec (fun () -> T.undo ~old_trail:T.empty ()) () in
  let next_solution = exec next_alt in
  incr max_runtime_id;
  { search; next_solution; destroy; exec; get }
;;

do_make_runtime := make_runtime;;

end (* }}} *)
open Mainloop

(******************************************************************************
  API
 ******************************************************************************)

let mk_outcome search get_cs assignments depth =
 try
   let alts = search () in
   let syn_csts, reloc_state, final_state, pp_ctx = get_cs () in
   let solution = {
     assignments;
     constraints = syn_csts;
     state = final_state;
     pp_ctx = pp_ctx;
     state_for_relocation = reloc_state;
   } in
   Success solution, alts
 with
 | No_clause (*| Non_linear*) -> Failure, noalts
 | No_more_steps -> NoMoreSteps, noalts

let execute_once ?max_steps ?delay_outside_fragment exec =
 let { search; get } = make_runtime ?max_steps ?delay_outside_fragment exec in
 try
   let result = fst (mk_outcome search (fun () -> get CS.Ugly.delayed, (exec.initial_depth,get C.table), get CS.state |> State.end_execution, { Data.uv_names = ref (get Pp.uv_names); table = get C.table }) exec.assignments exec.initial_depth) in
   [%end_trace "execute_once" ~rid];
   result
 with e ->
  [%end_trace "execute_once" ~rid];
  raise e

;;

let execute_loop ?delay_outside_fragment exec ~more ~pp =
 let { search; next_solution; get; destroy = _ } = make_runtime ?delay_outside_fragment exec in
 let k = ref noalts in
 let do_with_infos f =
   let time0 = Unix.gettimeofday() in
   let o, alts = mk_outcome f (fun () -> get CS.Ugly.delayed, (exec.initial_depth,get C.table), get CS.state |> State.end_execution, { Data.uv_names = ref (get Pp.uv_names); table = get C.table }) exec.assignments exec.initial_depth in
   let time1 = Unix.gettimeofday() in
   k := alts;
   pp (time1 -. time0) o in
 do_with_infos search;
 while !k != noalts do
   if not(more()) then k := noalts else
   try do_with_infos (fun () -> next_solution !k)
   with
   | No_clause -> pp 0.0 Failure; k := noalts; [%end_trace "execute_loop" ~rid]
   | e -> pp 0.0 Failure; k := noalts; [%end_trace "execute_loop" ~rid]; raise e
 done
;;

let print_constraints () = CS.print Fmt.std_formatter (CS.contents ())
let pp_stuck_goal ?pp_ctx fmt s = CS.pp_stuck_goal ?pp_ctx fmt s
let is_flex = HO.is_flex
let deref_uv = HO.deref_uv
let deref_appuv = HO.deref_appuv
let deref_head = HO.deref_head
let full_deref = HO.full_deref ~adepth:0 empty_env
let eta_contract_flex = HO.eta_contract_flex
let make_runtime = Mainloop.make_runtime
let lp_list_to_list = Clausify.lp_list_to_list
let list_to_lp_list = HO.list_to_lp_list
let split_conj = Clausify.split_conj
let mkAppArg = HO.mkAppArg
let subst ~depth = HO.subst depth
let move = HO.move
let hmove = HO.hmove
let mkinterval = C.mkinterval
let mkAppL = C.mkAppL
let lex_insertion = lex_insertion

let expand_uv ~depth r ~lvl ~ano =
  let t, assignment = HO.expand_uv ~depth r ~lvl ~ano in
  option_iter (fun (r,_,assignment) -> r @:= assignment) assignment;
  t
let expand_appuv ~depth r ~lvl ~args =
  let t, assignment = HO.expand_appuv ~depth r ~lvl ~args in
  option_iter (fun (r,_,assignment) -> r @:= assignment) assignment;
  t

module CompileTime = struct
  let update_indexing = update_indexing
  let add_to_index = add_to_index
  let clausify1 = Clausify.clausify1  
end