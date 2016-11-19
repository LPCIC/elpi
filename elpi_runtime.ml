(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Fmt = Format
module F = Elpi_ast.Func
open Elpi_util

module IM = Map.Make(struct type t = int let compare x y = x - y end)

let { CData.cin = in_float; isc = is_float; cout = out_float } as cfloat =
  CData.(declare {
    data_name = "float";
    data_pp = (fun f x -> Fmt.fprintf f "%f" x);
    data_eq = (==);
    data_hash = Hashtbl.hash;
  })
let { CData.cin = in_int; isc = is_int; cout = out_int } as cint =
  CData.(declare {
    data_name = "int";
    data_pp = (fun f x -> Fmt.fprintf f "%d" x);
    data_eq = (==);
    data_hash = Hashtbl.hash;
  })
let { CData.cin = in_string; isc = is_string; cout = out_string } as cstring =
  CData.(declare {
    data_name = "string";
    data_pp = (fun f x -> Fmt.fprintf f "\"%s\"" (F.show x));
    data_eq = (==);
    data_hash = Hashtbl.hash;
  })
let { CData.cin = in_loc; isc = is_loc; cout = out_loc } as cloc =
  CData.(declare {
    data_name = "loc";
    data_pp = (fun f x ->
      Fmt.fprintf f "%s:%d:" (Ploc.file_name x) (Ploc.line_nb x));
    data_eq = (==);
    data_hash = Hashtbl.hash;
  })

(******************************************************************************
  Terms: data type definition and printing
 ******************************************************************************)

(* To break circularity, we open the index type (index of clauses) here
 * and extend it with the Index constructor when such data type will be
 * defined.  The same for chr with CHR.t *)
type prolog_prog = ..
let pp_prolog_prog = mk_extensible_printer ()
type chr = ..
let pp_chr = mk_extensible_printer ()

(* Used by pretty printers, to be later instantiated in module Constants *)
let pp_const = mk_extensible_printer ()
type constant = int (* De Bruijn levels *)
[@printer (pp_extensible pp_const)]
[@@deriving show, eq]

(* To be instantiated after the dummy term is defined *)
let pp_oref = mk_extensible_printer ()

(* Invariant: a Heap term never points to a Query term *)
let id_term = UUID.make ()
type term =
  (* Pure terms *)
  | Const of constant
  | Lam of term
  | App of constant * term * term list
  (* Clause terms: unif variables used in clauses *)
  | Arg of (*id:*)int * (*argsno:*)int
  | AppArg of (*id*)int * term list
  (* Heap terms: unif variables in the query *)
  | UVar of term_attributed_ref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term_attributed_ref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | CData of CData.t
  (* Optimizations *)
  | Cons of term * term
  | Nil
and term_attributed_ref = {
  mutable contents : term [@printer (pp_extensible_any ~id:id_term pp_oref)];
  mutable rest : stuck_goal list [@printer fun _ _ -> ()]
                                 [@equal fun _ _ -> true];
}
and stuck_goal = {
  mutable blockers : term_attributed_ref list;
  kind : stuck_goal_kind;
}
and stuck_goal_kind =
 | Constraint of constraint_def (* inline record in 4.03 *)
 | Unification of unification_def 
and unification_def = {
  adepth : int;
  env : term array;
  bdepth : int;
  a : term;
  b : term;
}
and constraint_def = {
  depth : int;
  prog : prolog_prog [@equal fun _ _ -> true]
               [@printer (pp_extensible pp_prolog_prog)];
  pdiff : (int * term) list;
  goal : term;
}
[@@deriving show, eq]

let destConst = function Const x -> x | _ -> assert false

(* Our ref data type: creation and dereference.  Assignment is defined
   After the constraint store, since assigning may wake up some constraints *)
let oref x = { contents = x; rest = [] }
let (!!) { contents = x } = x

(* Arg/AppArg point to environments, here the empty one *)
type env = term array
let empty_env = [||]

(* - negative constants are global names
   - constants are hashconsed (terms)
   - we use special constants to represent !, pi, sigma *)
module Constants : sig

  val funct_of_ast : F.t -> constant * term
  val of_dbl : constant -> term
  val show : constant -> string
  val pp : Format.formatter -> constant -> unit
  val fresh : unit -> constant * term
  val from_string : string -> term
  val from_stringc : string -> constant
 
  (* To keep the type of terms small, we use special constants for !, =, pi.. *)
  (* {{{ *)
  val cutc   : term
  val truec  : term
  val andc   : constant
  val andt   : term
  val andc2  : constant
  val orc    : constant
  val implc  : constant
  val rimplc  : constant
  val rimpl  : term
  val pic    : constant
  val pi    : term
  val sigmac : constant
  val eqc    : constant
  val rulec : constant
  val cons : term
  val consc : constant
  val nil : term
  val nilc : constant
  val entailsc : constant
  val nablac : constant
  val uvc : constant
  val asc : constant
  val letc : constant
  val arrowc : constant

  val spillc : constant
  (* }}} *)

  (* Value for unassigned UVar/Arg *)
  val dummy  : term

  type t = constant
  val compare : t -> t -> int

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t

  (* mkinterval d n 0 = [d; ...; d+n-1] *)
  val mkinterval : int -> int -> int -> term list

end = struct (* {{{ *)

(* Hash re-consing :-( *)
let funct_of_ast, of_dbl, show, fresh =
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
   Hashtbl.add h' n (F.show x);
   Hashtbl.add h'' n xx;
   Hashtbl.add h x p; p),
 (function x ->
  try Hashtbl.find h'' x
  with Not_found ->
   let xx = Const x in
   Hashtbl.add h' x ("x" ^ string_of_int x);
   Hashtbl.add h'' x xx; xx),
 (function n ->
   try Hashtbl.find h' n
   with Not_found -> string_of_int n),
 (fun () ->
   decr fresh;
   let n = !fresh in
   Hashtbl.add h' n ("frozen-"^string_of_int n);
   n,Const n)
;;

let pp fmt c = Format.fprintf fmt "%s" (show c)

let from_stringc s = fst (funct_of_ast F.(from_string s))
let from_string s = snd (funct_of_ast F.(from_string s))

let cutc = snd (funct_of_ast F.cutf)
let truec = snd (funct_of_ast F.truef)
let andc, andt = funct_of_ast F.andf
let andc2 = fst (funct_of_ast F.andf2)
let orc = fst (funct_of_ast F.orf)
let implc = fst (funct_of_ast F.implf)
let rimplc, rimpl = funct_of_ast F.rimplf
let pic, pi = funct_of_ast F.pif
let sigmac = fst (funct_of_ast F.sigmaf)
let eqc = fst (funct_of_ast F.eqf)
let rulec = fst (funct_of_ast (F.from_string "rule"))
let nilc, nil = (funct_of_ast F.nilf)
let consc, cons = (funct_of_ast F.consf)
let nablac = fst (funct_of_ast (F.from_string "nabla"))
let entailsc = fst (funct_of_ast (F.from_string "?-"))
let uvc = fst (funct_of_ast (F.from_string "??"))
let asc = fst (funct_of_ast (F.from_string "as"))
let letc = fst (funct_of_ast (F.from_string ":="))
let spillc = fst (funct_of_ast (F.spillf))
let arrowc = fst (funct_of_ast F.arrowf)

let dummy = App (-9999,cutc,[])

module Self = struct
  type t = constant
  let compare x y = x - y
end

module Map = Map.Make(Self)
module Set = Set.Make(Self)

include Self

let () = extend_printer pp_const (fun fmt i ->
  Fmt.fprintf fmt "%s" (show i);
  `Printed)

(* mkinterval d n 0 = [d; ...; d+n-1] *)
let rec mkinterval depth argsno n =
 if n = argsno then []
 else of_dbl (n+depth)::mkinterval depth argsno (n+1)
;;

end (* }}} *)
module C = Constants

(* true=input, false=output *)
type mode = bool list [@@deriving show]

type mode_decl =
  | Mono of mode
  | Multi of (constant * (constant * constant) list) list

(* An elpi program, as parsed.  But for idx and query_depth that are threaded
   around in the main loop, chr and modes are globally stored in Constraints
   and Clausify. *)
type program = {
  (* n of sigma/local-introduced variables *)
  query_depth : int;
  (* the lambda-Prolog program: an indexed list of clauses *) 
  prolog_program : prolog_prog [@printer (pp_extensible pp_prolog_prog)];
  (* constraint handling rules *)
  chr : chr [@printer (pp_extensible pp_chr)];
  modes : mode_decl C.Map.t; 
}
type query = string list * int * env * term
exception No_clause

(* Dereferencing an UVar(r,args) when !!r != dummy requires a function
   of this kind.  The pretty printer needs one but will only be defined
   later, since we need, for example, beta reduction to implement it *)
type 'args deref_fun =
  ?avoid:term_attributed_ref -> from:int -> to_:int -> 'args -> term -> term

module Pp : sig
 
  (* Low level printing *)
  val ppterm :
    (*depth:*)int -> (*names:*)string list -> (*argsdepth:*)int -> env ->
    Fmt.formatter -> term -> unit

  (* For user consumption *)
  val uppterm :
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

let min_prec = Elpi_parser.min_precedence
let appl_prec = Elpi_parser.appl_precedence
let lam_prec = Elpi_parser.lam_precedence
let inf_prec = Elpi_parser.inf_precedence

let xppterm ~nice depth0 names argsdepth env f t =
  let pp_app f pphd pparg ?pplastarg (hd,args) =
   if args = [] then pphd f hd
   else
    Fmt.fprintf f "@[<hov 1>%a@ %a@]" pphd hd
     (pplist pparg ?pplastelem:pplastarg "") args in
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
     Fmt.fprintf f "%s%s" s
      (if vardepth=0 then "" else "^" ^ string_of_int vardepth)
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
      pplist ~boxed:true (aux Elpi_parser.list_element_prec depth) "," f prefix ;
      if last != Nil then begin
       Fmt.fprintf f " | " ;
       aux prec 1 f last
      end;   
      Fmt.fprintf f "]"
    | Const s -> ppconstant f s 
    | App (hd,x,xs) ->
       (try
         let assoc,hdlvl =
          Elpi_parser.precedence_of (F.from_string (C.show hd)) in
         with_parens hdlvl
         (fun _ -> match assoc with
            Elpi_parser.Infix when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Elpi_parser.Infixl when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux hdlvl depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Elpi_parser.Infixr when List.length xs = 1 ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux hdlvl depth) (List.hd xs)
          | Elpi_parser.Prefix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" ppconstant hd
              (aux hdlvl depth) x
          | Elpi_parser.Postfix when xs = [] ->
             Fmt.fprintf f "@[<hov 1>%a@ %a@]" (aux hdlvl depth) x
              ppconstant hd 
          | _ ->
             pp_app f ppconstant (aux inf_prec depth)
              ~pplastarg:(aux_last inf_prec depth) (hd,x::xs))
        with Not_found -> 
         let lastarg = List.nth (x::xs) (List.length xs) in
         let hdlvl =
          if is_lambda depth lastarg then lam_prec
          else appl_prec in
         with_parens hdlvl (fun _ ->
          pp_app f ppconstant (aux inf_prec depth)
           ~pplastarg:(aux_last inf_prec depth) (hd,x::xs)))
    | Custom (hd,xs) ->
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
        let c = C.of_dbl depth in
        Fmt.fprintf f "%a \\@ %a" (aux inf_prec depth) c
         (aux min_prec (depth+1)) t)
    | CData d -> CData.pp f d
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

(* Together to hide low level APIs of ConstraintStore needed by Trail *)
module ConstraintStoreAndTrail : sig

  type propagation_item = {
     cstr : constraint_def;
     cstr_position : int;
  }

  val new_delayed      : propagation_item list ref
  val to_resume        : stuck_goal list ref

  val pivot : old:term_attributed_ref -> term_attributed_ref -> stuck_goal list -> stuck_goal list

  val declare_new : stuck_goal -> unit
  val remove_old : stuck_goal -> unit
  val remove_old_constraint : constraint_def -> unit

  val contents : unit -> constraint_def list
  val print : Fmt.formatter -> unit

  module Custom : sig
    type 'a constraint_type

    (* Must be purely functional *)
    val declare_constraint :
      name:string ->
      pp:(Fmt.formatter -> 'a -> unit) ->
      empty:'a ->
        'a constraint_type

    val update : 'a constraint_type -> ('a -> 'a) -> unit
    val read : 'a constraint_type -> 'a
  end
  type custom_constraints
  val custom_constraints : custom_constraints Fork.local_ref

  (* ---------------------------------------------------- *)

  type trail_item =
  | Assignement of term_attributed_ref
  | StuckGoalAddition of stuck_goal
  | StuckGoalRemoval of stuck_goal
  type trail = trail_item list
  val pp_trail_item : Fmt.formatter -> trail_item -> unit

  (* Exposed to save a copy, not to modify  XXX 4.03 [@inline] get_trail *)
  val trail : trail Fork.local_ref
  val empty_trail : trail Fork.local_ref

  (* If true, no need to trail an imperative action.  Not part of trial_this
   * because you can save allocations and a function call by testing locally *)
  val last_call : bool ref

  (* add an item to the trail  XXX 4.03 [@inline] *)
  val trail_this : trail_item -> unit

  (* backtrack *)
  val undo :
    old_trail:trail -> ?old_constraints:custom_constraints -> unit -> unit

  val print_trail : Fmt.formatter -> unit

  (* ---------------------------------------------------- *)

  (* This is only used to know if the program execution is really over,
     I.e. to implement the last component of the runtime data type *)
  module Ugly : sig val delayed : stuck_goal list ref end

end = struct (* {{{ *)

 type propagation_item = {
    cstr : constraint_def;
    cstr_position : int;
 }

  type custom_constraints = Obj.t IM.t
  let custom_constraints = Fork.new_local IM.empty
  let custom_constraints_declarations = ref IM.empty
  module Custom = struct
    type 'a constraint_type = int

    let cid = ref 0
    let declare_constraint ~name ~pp ~empty =
      incr cid;
      custom_constraints_declarations :=
        IM.add !cid (name,Obj.repr pp, Obj.repr empty) !custom_constraints_declarations;
      !cid

    let find id =
      try IM.find id !custom_constraints
      with Not_found ->
        let _, _, init = IM.find id !custom_constraints_declarations in
        init

    let update id f =
      custom_constraints :=
        IM.add id (Obj.repr (f (Obj.obj (find id)))) !custom_constraints
    let read id = Obj.obj (find id)
  end

type trail_item =
| Assignement of term_attributed_ref
| StuckGoalAddition of stuck_goal
| StuckGoalRemoval of stuck_goal
[@@deriving show]

type trail = trail_item list
[@@deriving show]

let trail = Fork.new_local []
let empty_trail = Fork.new_local []
let last_call = Fork.new_local false;;

module Ugly = struct let delayed : stuck_goal list ref = Fork.new_local [] end
open Ugly
let contents () =
  map_filter (function { kind = Constraint c } -> Some c | _ -> None) !delayed

let trail_this i = 
  [%spy "trail-this" (fun fmt i ->
     Fmt.fprintf fmt "last_call:%b item:%a" !last_call pp_trail_item i) i];
  if not !last_call then trail := i :: !trail ;;

let remove ({ blockers } as sg) =
 [%spy "remove" (fun fmt -> Fmt.fprintf fmt "%a" pp_stuck_goal) sg];
 delayed := remove_from_list sg !delayed;
 List.iter (fun r -> r.rest <- remove_from_list sg r.rest) blockers

let add ({ blockers } as sg) =
 [%spy "add" (fun fmt -> Fmt.fprintf fmt "%a" pp_stuck_goal) sg];
 delayed := sg :: !delayed;
 List.iter (fun r -> r.rest <- sg :: r.rest) blockers

let new_delayed = Fork.new_local []
let to_resume = Fork.new_local []

let print_trail fmt =
  pp_trail fmt !trail;
  Fmt.fprintf fmt "to_resume:%d new_delayed:%d\n%!"
    (List.length !to_resume) (List.length !new_delayed)

let pivot ~old:r r1 sg =
  let rc = ref [] in
  List.iter (fun d ->
    if List.memq d sg then begin
      d.blockers <- List.map (fun v -> if v == r then r1 else v) d.blockers;
      rc := d :: !rc
    end) !delayed;
  List.rev !rc

let declare_new cstr =
  add cstr ;
  begin match cstr.kind with
  | Unification _ -> ()
  | Constraint cstr ->
      new_delayed := { cstr; cstr_position = 0} :: !new_delayed
  end;
  trail_this (StuckGoalAddition cstr)

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
  trail_this (StuckGoalRemoval cstr)
;;

let remove_old_constraint cd =
  let c = List.find
    (function { kind = Constraint x } -> x == cd | _ -> false) !delayed in
  remove_old c

let undo ~old_trail ?old_constraints () =
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
       (match r.contents with
       | UVar({ rest = _ :: _ } as r',_,_)
       | AppUVar({ rest = _ :: _ } as r',_,_) -> r.rest <- pivot ~old:r' r r'.rest
       | _ -> ());
       r.contents <- C.dummy;
       trail := rest
    | StuckGoalAddition sg :: rest -> remove sg; trail := rest
    | StuckGoalRemoval sg :: rest -> add sg; trail := rest
    | [] -> anomaly "undo to unknown trail"
  done;
  match old_constraints with
  | Some old_constraints -> custom_constraints := old_constraints
  | None -> ()
;;

let print fmt =
 List.iter (function
   | { kind = Unification { adepth = ad; env = e; bdepth = bd; a; b } ; blockers = l } ->
      Fmt.fprintf fmt
       "delayed goal: @[<hov 2>^%d:%a@ == ^%d:%a on %a@]\n%!"
        ad (uppterm ad [] 0 empty_env) a
        bd (uppterm ad [] ad e) b
        (pplist (uppterm ad [] 0 empty_env) ",")
        (List.map (fun r -> UVar(r,0,0)) l)
   | { kind = Constraint { depth; pdiff; goal = g } ; blockers = l } ->
      Fmt.fprintf fmt
        "delayed goal: @[<hov 2> %a@ ⊢ %a on %a@]\n%!"
          (pplist (fun fmt (depth,t) -> uppterm depth [] 0 empty_env fmt t) ",") pdiff
          (uppterm depth [] 0 empty_env) g
          (pplist (uppterm depth [] 0 empty_env) ",")
          (List.map (fun r -> UVar(r,0,0)) l)
       (* CSC: Bug here: print at the right precedence *)
   ) !delayed
  ;;

end (* }}} *)
module T  = ConstraintStoreAndTrail
module CS = ConstraintStoreAndTrail

(* Assigning an UVar wakes up suspended goals/constraints *)
let (@:=) r v =
  if r.rest <> [] then
    begin
    [%spy "assign-to_resume" (fun fmt l ->
        Fmt.fprintf fmt "%d" (List.length l)) r.rest];
     CS.to_resume := r.rest @ !CS.to_resume
    end;
 r.contents <- v
;;

(* UVar 2 UVar assignment, constraints are inherited *)
let (@:==) r v r1 =
  if r.rest <> [] then
    begin
    r1.rest <- CS.pivot r r1 r.rest;
    (* r.rest <- []; FIXME *)
    end;
 r.contents <- v
;;

module CHR : sig

  (* a set of rules *)
  type t

  (* a set of predicates contributing to represent a constraint *)
  type clique 

  type rule = (term, int) Elpi_ast.chr

  val empty : t

  val new_clique : constant list -> t -> t * clique
  val clique_of : constant -> t -> C.Set.t
  val add_rule : clique -> rule -> t -> t
  
  val rules_for : constant -> t -> rule list

  (* to store CHR.t in program *)
  val wrap_chr : t -> chr
  val unwrap_chr : chr -> t

end = struct (* {{{ *)

  type rule = (term, int) Elpi_ast.chr
  type t = { cliques : C.Set.t C.Map.t; rules : rule list C.Map.t }
  type clique = C.Set.t

  type chr += Chr of t
  let () = extend_printer pp_chr (fun fmt -> function
    | Chr c -> Fmt.fprintf fmt "<CHRs>";`Printed
    | _ -> `Passed)
  let wrap_chr x = Chr x
  let unwrap_chr = function Chr x -> x | _ -> assert false

  let empty = { cliques = C.Map.empty; rules = C.Map.empty }

  let new_clique cl ({ cliques } as chr) =
    if cl = [] then error "empty clique";
    let c = List.fold_right C.Set.add cl C.Set.empty in
    if C.Map.exists (fun _ c' -> not (C.Set.is_empty (C.Set.inter c c'))) cliques then
            error "overlapping constraint cliques";
    let cliques =
      List.fold_right (fun x cliques -> C.Map.add x c cliques) cl cliques in
    { chr with cliques }, c

  let clique_of c { cliques } =
    try C.Map.find c cliques with Not_found -> C.Set.empty

  let add_rule cl r ({ rules } as chr) =
    let rules = C.Set.fold (fun c rules ->
      try      
        let rs = C.Map.find c rules in
        C.Map.add c (rs @ [r]) rules
      with Not_found -> C.Map.add c [r] rules)
      cl rules in
    { chr with rules }


  let rules_for c { rules } =
    try C.Map.find c rules
    with Not_found -> []

end (* }}} *)

(******************************************************************************
  Unification (dereferencing and lift, to_heap)
 ******************************************************************************)

module HO : sig

  val unif : ?matching:bool -> int -> env -> int -> term -> term -> bool

  (* lift/restriction/heapification with occur_check *)
  val move : 
    adepth:int -> env -> ?avoid:term_attributed_ref -> ?depth:int ->
    from:int -> to_:int -> term -> term
  
  (* like move but for heap terms (no heapification) *)
  val hmove :
    ?avoid:term_attributed_ref ->
    from:int -> to_:int -> term -> term

  (* simultaneous substitution *)
  val subst : int -> term list -> term -> term

  val deref_uv : int deref_fun
  val deref_appuv : term list deref_fun

  val mkAppUVar : term_attributed_ref -> int -> term list -> term
  val mkAppArg : int -> int -> term list -> term
  val is_flex : term -> term_attributed_ref option
  val list_to_lp_list : term list -> term
    
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
 | UVar ({ contents = t} ,_,_)::tl -> (* ??? XXX *)
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
  | Custom (_,l) -> List.iter aux l
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
      assigment X^0 := to_heap ~from:1 ~to_:0 A^1
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
       if c >= from then C.of_dbl (c - delta) else (* locally bound *)
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
    | Custom (c,l) ->
       let l' = smart_map (maux e depth) l in
       if l == l' then x else Custom (c,l')
    | CData _ -> x
    | Cons(hd,tl) ->
       let hd' = maux e depth hd in
       let tl' = maux e depth tl in
       if hd == hd' && tl == tl' then x else Cons(hd',tl')
    | Nil -> x

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
       if argsdepth < to_ then anomaly "move: invalid Arg heapification";
       let r = oref C.dummy in
       let v = UVar(r,to_,0) in
       e.(i) <- v;
       if args == 0 then v else UVar(r,to_,args)
    | AppArg(i, args) when
      List.for_all (deterministic_restriction e ~args_safe:(argsdepth=to_)) args
      ->
       (* assign to UVar whose depth is greater than the current goal depth *)
       if argsdepth < to_ then anomaly "move: invalid AppArg heapification";
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
       if delta <= 0 then
         if vardepth + argsno <= from then x
         else
           let r,vardepth,argsno =
             decrease_depth r ~from:vardepth ~to_:from argsno in
           let args = C.mkinterval vardepth argsno 0 in
           let args = List.map (maux empty_env depth) args in
           mkAppUVar r vardepth args
       else
         if vardepth + argsno <= to_ then x
         else begin
           (* TODO/BUG: I believe this assert to be false; if it is, the
              code below is wrong when the assert fails *)
           assert (vardepth+argsno <= from);
           let assignment,fresh = make_lambdas (to_-argsno) argsno in
           if not !T.last_call then
            T.trail := (T.Assignement r) :: !T.trail;
           r @:= assignment;
          (* TODO: test if it is more efficient here to return fresh or
             the original, imperatively changed, term. The current solution
             avoids dereference chains, but puts more pressure on the GC. *)
           fresh
         end

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
       else if List.for_all (deterministic_restriction e ~args_safe:(argsdepth=to_)) args then
         (* TODO: this branch is to be reviewed/tested throughly, unless
            Enrico is now confident with it *)
         let args =
           try List.map (maux e depth) args
           with RestrictionFailure ->
             anomaly "TODO: implement deterministic restriction" in
         if vardepth <= to_ then mkAppUVar r vardepth args
         else
           let newvar = UVar(oref C.dummy,to_,0) in
           if not !T.last_call then T.trail := (T.Assignement r) :: !T.trail;
           r @:= newvar;
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
  if not !T.last_call then
   T.trail := (T.Assignement r) :: !T.trail;
  (r @:== newvar) newr;
  newr,to_,newargsno

(* simultaneous substitution of ts for [depth,depth+|ts|)
   the substituted term must be in the heap
   the term is delifted by |ts|
   every t in ts must be either an heap term or an Arg(i,0)
   the ts are lifted as usual *)
and subst fromdepth ts t =
 [%trace "subst" ("@[<hov 2>t: %a@ ts: %a@]"
   (uppterm (fromdepth+1) [] 0 empty_env) t (pplist (uppterm 0 [] 0 empty_env) ",") ts)
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
      else C.of_dbl (c-len) (* NOT LIFTED *)
   | Arg _ | AppArg _ -> anomaly "subst takes a heap term"
   | App(c,x,xs) as orig ->
      let x' = aux depth x in
      let xs' = List.map (aux depth) xs in
      let xxs' = x'::xs' in
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
        | Arg(i,0) -> mkAppArg i fromdepth xxs'
        | t ->
           let t = hmove ~from:fromdepth ~to_:depth t in
           beta depth [] t xxs'
      else if c < fromdepth then
        if x==x' && xs==xs' then orig else App(c,x',xs')
      else App(c-len,x',xs')
   | Custom(c,xs) as orig ->
      let xs' = List.map (aux depth) xs in
      if xs==xs' then orig else Custom(c,xs')
   | Cons(hd,tl) as orig ->
       let hd' = aux depth hd in
       let tl' = aux depth tl in
       if hd == hd' && tl == tl' then orig else Cons(hd',tl')
   | Nil -> Nil
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
     (uppterm depth [] 0 empty_env) t (pplist (uppterm depth [] 0 empty_env) ",") args)
 begin match t,args with
 | Lam t',hd::tl -> [%tcall beta depth (hd::sub) t' tl]
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
         | Custom (c,args1) -> Custom (c,args1@args)
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
        App (c,C.of_dbl from, args)
     | App (c,arg,args2) ->
        let args = C.mkinterval from args' 0 in
        App (c,arg,args2 @ args)
     | Custom (c,args2) ->
        let args = C.mkinterval from args' 0 in
        Custom (c,args2 @ args)
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
     | CData _ -> t
     | Arg _ | AppArg _ -> assert false (* Uv gets assigned only heap term *)
  end]

;;

let () = Pp.do_deref := deref_uv;;
let () = Pp.do_app_deref := deref_appuv;;

(* }}} *)

(* {{{ ************** unification ******************************* *)

(* is_flex is to be called only on heap terms *)
let rec is_flex =
 function
  | Arg _ | AppArg _ -> anomaly "is_flex called on Args"
  | UVar ({ contents = t }, _, _)
  | AppUVar ({ contents = t }, _, _) when t != C.dummy -> is_flex t
  | UVar (r, _, _) | AppUVar (r, _, _) -> Some r
  | Const _ | Lam _ | App _ | Custom _ | CData _ | Cons _ | Nil -> None

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
    lvl (pplist (ppterm adepth [] bdepth e) "") args b
    (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%d |-> %d" x n) "") map) res];
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
    [%trace "bind" ("%b %d + %a = t:%a a:%d delta:%d d:%d w:%d b:%d"
        left gamma (pplist (fun fmt (x,n) -> Fmt.fprintf fmt "%a |-> %d"
        (ppterm a [] b e) (C.of_dbl x) n) "") l
        (ppterm a [] b empty_env) t a delta d w b) begin
    match t with
    | UVar (r1,_,_) | AppUVar (r1,_,_) when r == r1 -> raise RestrictionFailure
    | Const c -> let n = cst c b delta in if n < 0 then C.of_dbl n else Const n
    | Lam t -> Lam (bind b delta (w+1) t)
    | App (c,t,ts) -> App (cst c b delta, bind b delta w t, List.map (bind b delta w) ts)
    | Cons(hd,tl) -> Cons(bind b delta w hd, bind b delta w tl)
    | Nil -> t
    | Custom (c, tl) -> Custom(c, List.map (bind b delta w) tl)
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
    | (UVar _ | AppUVar _ | Arg _ | AppArg _) as _orig_ ->
        (* We deal with all flexible terms in a uniform way *)
        let r, lvl, (is_llam, args), orig_args = match _orig_ with
          | UVar(r,lvl,0) -> r, lvl, (true, []), []
          | UVar(r,lvl,args) ->
              let r' = oref C.dummy in
              let v = UVar(r',lvl+args,0) in
              r @:= mknLam args v;
              if not !T.last_call then T.trail := (T.Assignement r) :: !T.trail;
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
        if is_llam then begin
          let n_args = List.length args in
          if lvl > gamma then
            (* All orig args go away, but some between gamma and lvl can stay
             * if they are in l *)
            let args_gamma_lvl_abs, args_gamma_lvl_here =
              let rec keep_cst_for_lvl = function
                | [] -> []
                | (i,i_p) :: rest ->
                    if i > lvl then keep_cst_for_lvl rest
                    else
                      (C.of_dbl i, C.of_dbl (cst ~hmove:false i b delta))
                        :: keep_cst_for_lvl rest in
              List.split (keep_cst_for_lvl (List.sort Pervasives.compare l)) in
            let r' = oref C.dummy in
            r @:= mknLam n_args (mkAppUVar r' gamma args_gamma_lvl_abs);
            if not !T.last_call then T.trail := (T.Assignement r) :: !T.trail;
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
                    else if c >= a + d then c + new_lams - (a+d - gamma)
                    else pos c + gamma in
                  C.of_dbl (c_p + lvl) :: a_lvl,
                  C.of_dbl i :: a_here
                with RestrictionFailure -> acc) args ([],[]) in
            if n_args = List.length args_here then
              (* no pruning, just binding the args as a normal App *)
              mkAppUVar r lvl (List.map (bind b delta w) orig_args)
            else
              (* we need to project away some of the args *)
              let r' = oref C.dummy in
              let v = mkAppUVar r' lvl args_lvl in
              r @:= mknLam n_args v;
              if not !T.last_call then T.trail := (T.Assignement r) :: !T.trail;
              (* This should be the beta reduct. One could also
               * return the non reduced but bound as in the other if branch *)
              mkAppUVar r' lvl args_here
        end
          else raise RestrictionFailure
  end] in
  try
    r @:= mknLam new_lams (bind b delta 0 t);
    if not !T.last_call then T.trail := (T.Assignement r) :: !T.trail;
    [%spy "assign(HO)" (ppterm gamma [] a empty_env) (!!r)];
    true
  with RestrictionFailure -> [%spy "bind result" (fun fmt x -> Fmt.fprintf fmt "%b" x) false];false
;;
(* exception Non_linear *)

let rec list_to_lp_list = function
  | [] -> Nil
  | x::xs -> Cons(x,list_to_lp_list xs)
;;

let delay_hard_unif_problems = Fork.new_local false

let rec unif matching depth adepth a bdepth b e =
   [%trace "unif" ("@[<hov 2>^%d:%a@ =%d%s= ^%d:%a@]%!"
       adepth (ppterm (adepth+depth) [] adepth empty_env) a
       depth (if matching then "m" else "")
       bdepth (ppterm (bdepth+depth) [] adepth e) b)
   begin let delta = adepth - bdepth in
   (delta = 0 && a == b) || match a,b with
  
   (* _ as X binding *)
   | _, App(c,arg,[(Arg _ | AppArg _) as as_this]) when c == C.asc ->
      unif matching depth adepth a bdepth arg e &&
      unif matching depth adepth a bdepth as_this e 
   | _, App(c,arg,_) when c == C.asc -> error "syntax error in as"
   | App(c,arg,_), _ when c == C.asc ->
      unif matching depth adepth arg bdepth b e

(* TODO: test if it is better to deref_uv first or not, i.e. the relative order
   of the clauses below *)
   | UVar(r1,_,args1), UVar(r2,_,args2) when r1 == r2 -> args1 == args2
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

   (* UVar introspection *)
   | (UVar _ | AppUVar _), Const c when c == C.uvc && matching -> true
   | UVar(r,vd,ano), App(c,hd,[]) when c == C.uvc && matching ->
      unif matching depth adepth (UVar(r,vd,ano)) bdepth hd e
   | AppUVar(r,vd,_), App(c,hd,[]) when c == C.uvc && matching ->
      unif matching depth adepth (UVar(r,vd,0)) bdepth hd e
   | UVar(r,vd,ano), App(c,hd,[arg]) when c == C.uvc && matching ->
      unif matching depth adepth a bdepth hd e &&
      unif matching depth adepth Nil bdepth arg e
   | AppUVar(r,vd,args), App(c,hd,[arg]) when c == C.uvc && matching ->
      unif matching depth adepth (UVar(r,vd,0)) bdepth hd e &&
      let args = list_to_lp_list args in
      unif matching depth adepth args bdepth arg e
   | _, (Const c | App(c,_,_)) when c == C.uvc -> false
   (*
      error (show uvc ^ " can be used only in matching and takes 0, 1 or 2 args " ^ show_term a)

*)
   (* assign *)
   | _, Arg (i,0) ->
     begin try
      e.(i) <- hmove ~from:(adepth+depth) ~to_:adepth a;
      [%spy "assign" (ppterm adepth [] adepth empty_env) (e.(i))]; true
     with RestrictionFailure -> false end
   | UVar({ rest = [] },_,0), UVar ({ rest = _ :: _ },_,0) -> unif matching depth bdepth b adepth a e
   | AppUVar({ rest = [] },_,_), UVar ({ rest = _ :: _ },_,0) -> unif matching depth bdepth b adepth a e
   | _, UVar (r,origdepth,0) ->
       if not !T.last_call then
        T.trail := (T.Assignement r) :: !T.trail;
       begin try
         let t =
           if depth = 0 then
             hmove ~avoid:r ~from:adepth ~to_:origdepth a
           else
             (* First step: we lift the l.h.s. to the r.h.s. level *)
             let a = hmove ~avoid:r ~from:adepth ~to_:bdepth a in
             (* Second step: we restrict the l.h.s. *)
             hmove ~from:(bdepth+depth) ~to_:origdepth a in
         r @:= t;
         [%spy "assign" (fun fmt tt -> Fmt.fprintf fmt "%a := %a" (ppterm depth [] bdepth empty_env) (UVar (r,origdepth,0)) (ppterm depth [] adepth empty_env) tt) t]; true
       with RestrictionFailure -> false end
   | UVar (r,origdepth,0), _ when not matching ->
       if not !T.last_call then
        T.trail := (T.Assignement r) :: !T.trail;
       begin try
         let t =
           if depth=0 then
             move ~avoid:r ~adepth ~from:bdepth ~to_:origdepth e b
           else
             (* First step: we lift the r.h.s. to the l.h.s. level *)
             let b = move ~avoid:r ~adepth ~from:bdepth ~to_:adepth e b in
             (* Second step: we restrict the r.h.s. *)
             hmove ~from:(adepth+depth) ~to_:origdepth b in
         r @:= t;
         [%spy "assign" (fun fmt tt -> Fmt.fprintf fmt "%a := %a" (ppterm depth [] adepth empty_env) (UVar (r,origdepth,0)) (ppterm depth [] adepth empty_env) tt) t]; true
       with RestrictionFailure -> false end

   (* simplify *)
   (* TODO: unif matching->deref_uv case. Rewrite the code to do the job directly? *)
   | _, Arg (i,args) ->
      e.(i) <- fst (make_lambdas adepth args);
      [%spy "assign" (ppterm depth [] adepth empty_env) (e.(i))];
      unif matching depth adepth a bdepth b e
   | UVar({ rest = [] },_,a1), UVar ({ rest = _ :: _ },_,a2) when a1 + a2 > 0 -> unif matching depth bdepth b adepth a e
   | AppUVar({ rest = [] },_,_), UVar ({ rest = _ :: _ },_,a2) when  a2 > 0 -> unif matching depth bdepth b adepth a e
   | _, UVar (r,origdepth,args) when args > 0 ->
      if not !T.last_call then
       T.trail := (T.Assignement r) :: !T.trail;
      r @:= fst (make_lambdas origdepth args);
      [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
      unif matching depth adepth a bdepth b e
   | UVar (r,origdepth,args), _ when args > 0 ->
      if not !T.last_call then
       T.trail := (T.Assignement r) :: !T.trail;
      r @:= fst (make_lambdas origdepth args);
      [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
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
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b} in
       let blockers =
         match is_flex other with
         | None -> [r]
         | Some r' -> if r==r' then [r] else [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else false
   | AppUVar({ rest = _ :: _ },_,_), (AppUVar ({ rest = [] },_,_) | UVar ({ rest = [] },_,_)) -> unif matching depth bdepth b adepth a e
   | AppUVar (r, lvl,args), other when not matching ->
       let is_llam, args = is_llam lvl args adepth bdepth depth true e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth true other e
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth empty_env) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b} in
       let blockers = match is_flex other with | None -> [r] | Some r' -> [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else false
   | other, AppUVar (r, lvl,args) ->
       let is_llam, args = is_llam lvl args adepth bdepth depth false e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth false other e
       else if !delay_hard_unif_problems then begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth e) b ;
       let kind = Unification {adepth = adepth+depth; env = e; bdepth = bdepth+depth; a; b} in
       let blockers =
         match is_flex other with
         | None -> [r]
         | Some r' -> if r==r' then [r] else [r;r'] in
       CS.declare_new { kind; blockers };
       true
       end else false
  
   (* recursion *)
   | App (c1,x2,xs), App (c2,y2,ys) ->
      (* Compressed cut&past from Const vs Const case below +
         delta=0 optimization for <c1,c2> and <x2,y2> *)
      ((delta=0 || c1 < bdepth) && c1=c2
       || c1 >= adepth && c1 = c2 + delta)
       &&
       (delta=0 && x2 == y2 || unif matching depth adepth x2 bdepth y2 e) &&
       for_all2 (fun x y -> unif matching depth adepth x bdepth y e) xs ys
   | Custom (c1,xs), Custom (c2,ys) ->
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
   | _ -> false
   end]
;;

(* FISSA PRECEDENZA PER AS e FISSA INDEXING per AS e fai coso generale in unif *)

let unif ?(matching=false) adepth e bdepth a b =
 let res = unif matching 0 adepth a bdepth b e in
 [%spy "unif result" (fun fmt x -> Fmt.fprintf fmt "%b" x) res];
 res
;;

(* Look in Git for Enrico's partially tail recursive but slow unification.
   The tail recursive version is even slower. *)

(* }}} *)

end
(* }}} *)
open HO

(******************************************************************************
  Indexing
 ******************************************************************************)

module type Indexing = sig

  type key
  val pp_key : key -> string

  (* a clause is: "key args :- hyps." the head is split into its main symbol
   * and its arguments.  This is because the unification/matching of the head
   * symbol is made by the indexing machinery.  We don't support unification
   * variables in head position *)
  type clause = {
    depth : int;
    args : term list;
    hyps : term list;
    vars : int;
    key : key;
    mode: mode;
  }
  val ppclause : Fmt.formatter -> clause -> unit

  type idx
  val key_of : mode:[`Query | `Clause] -> depth:int -> term -> key
  val hd_pred : clause -> constant
  val add_clauses : clause list -> (int * term) -> idx -> idx
  val get_clauses : depth:int -> term -> idx -> clause list
  val make_index : clause list -> idx
  val local_prog : idx -> ((*depth:*)int * term) list
end
module TwoMapIndexing : Indexing = struct (* {{{ *)

(* all clauses: used when the query is flexible
   all flexible clauses: used when the query is rigid and the map
                        for that atom is empty
   map: used when the query is rigid before trying the all flexible clauses *)
type key1 = int
type key2 = int
type key = key1 * key2

type clause = {
    depth : int;
    args : term list;
    hyps : term list;
    vars : int;
    key : key;
    mode: mode;
  }

let hd_pred { key = (hd,_) } = hd

type idx = {
  src : (int * term) list;
  map : (clause list * clause list * clause list Elpi_ptmap.t) Elpi_ptmap.t
}

let variablek =       -99999999 (* a flexible term like X t *)
let mustbevariablek = -99999998 (* ?? or ?? t or ?? l t *)
let abstractionk =    -99999997

let pp_key (hd,v) = C.show hd ^ "." ^
       if v == variablek then "(uvar)"
  else if v == abstractionk then "(lambda)"
  else if v < 0 then
    let s = C.show v in
    if Str.string_match (Str.regexp "^-?[0-9]*$") s 0 then "(cdata)"
    else s
  else "(heigen)"
  
let ppclause f { args = args; hyps = hyps; key = (hd,_) } =
  Fmt.fprintf f "@[<hov 1>%s %a :- %a.@]" (C.show hd)
     (pplist (uppterm 0 [] 0 empty_env) "") args
     (pplist (uppterm 0 [] 0 empty_env) ",") hyps

let key_of ~mode:_ ~depth =
 let rec skey_of = function
    Const k when k = C.uvc -> mustbevariablek
  | Const k -> k
  | Nil -> C.nilc
  | Cons _ -> C.consc
  | UVar ({contents=t},origdepth,args) when t != C.dummy ->
     skey_of (deref_uv ~from:origdepth ~to_:depth args t)
  | AppUVar ({contents=t},origdepth,args) when t != C.dummy ->
     skey_of (deref_appuv ~from:origdepth ~to_:depth args t)
  | App (k,_,_) when k = C.uvc -> mustbevariablek
  | App (k,a,_) when k = C.asc -> skey_of a
  | App (k,_,_)
  | Custom (k,_) -> k
  | Lam _ -> abstractionk
  | Arg _ | UVar _ | AppArg _ | AppUVar _ -> variablek
  | CData d -> 
     let hash = -(CData.hash d) in
     if hash > abstractionk then hash
     else hash+2 (* ?? *) in           
 let rec key_of_depth = function
   Const k -> k, variablek
 | UVar ({contents=t},origdepth,args) when t != C.dummy ->
    (* TODO: optimization: avoid dereferencing *)
    key_of_depth (deref_uv ~from:origdepth ~to_:depth args t)
 | AppUVar ({contents=t},origdepth,args) when t != C.dummy -> 
    key_of_depth (deref_appuv ~from:origdepth ~to_:depth args t)
 | App(k,arg,_) when k == C.asc -> key_of_depth arg
 | App (k,arg2,_) -> k, skey_of arg2
 | Custom _ -> assert false
 | Nil | Cons _ | Arg _ | AppArg _ | Lam _ | UVar _ | AppUVar _ | CData _->
    raise (Failure "Not a predicate")
 in
  key_of_depth
;;

let get_clauses ~depth a { map = m } =
 let ind,app = key_of ~mode:`Query ~depth a in
 let rc =
   try
    let l,flexs,h = Elpi_ptmap.find ind m in
    if app=variablek then l
    else (try Elpi_ptmap.find app h with Not_found -> flexs)
   with Not_found -> []
 in
 [%log "get_clauses" (pp_key (ind,app)) (List.length rc)];
 rc

let add_clauses clauses s { map = p;  src } =       
  let p = List.fold_left (fun m clause ->
    let matching = match clause.mode with [] -> false | x :: _ -> x in
    let ind,app = clause.key in
    try 
      let l,flexs,h = Elpi_ptmap.find ind m in
      (* X matches both rigid and flexible terms *)
      if app == variablek then begin
        Elpi_ptmap.add ind (clause :: l, clause :: flexs, Elpi_ptmap.map (fun l_rev -> clause::l_rev) h) m
      (* ?? matches only flexible terms *)
      end else if app == mustbevariablek then begin
        Elpi_ptmap.add ind (clause :: l, flexs, h) m
      (* a rigid term matches flexible terms only in unification mode *)
      end else begin
        let l_rev = try Elpi_ptmap.find app h with Not_found -> flexs in
        let l = if matching then l else clause :: l in
        Elpi_ptmap.add ind (l, flexs, Elpi_ptmap.add app (clause::l_rev) h) m
      end
    with
    | Not_found -> 
     if app=variablek then
      Elpi_ptmap.add ind ([clause],[clause],Elpi_ptmap.empty) m
     else if app=mustbevariablek then
      Elpi_ptmap.add ind ([clause],[],Elpi_ptmap.empty) m
     else
      let l = if matching then [] else [clause] in
      Elpi_ptmap.add ind
       (l,[],Elpi_ptmap.add app [clause] Elpi_ptmap.empty) m
    ) p clauses
  in
  { map = p; src = s :: src }

let make_index p =
  let idx = add_clauses (List.rev p) (0,C.cutc) { map = Elpi_ptmap.empty; src = [] } in
  { idx with src = [] } (* original program not in clauses *)
 
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
    | Const c -> C.of_dbl (fix_const c)
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
    | Custom(c,xs) -> Custom(c,List.map aux xs)
    | UVar(_,_,_) as orig ->
       (* TODO: quick hack here, but it does not work for AppUVar *)
       hmove ~from:depth ~to_:(depth+vars) orig
    | AppUVar(r,vardepth,args) ->
       assert false (* TODO, essentialy almost copy the code from move delta < 0 *)
    | Cons(hd,tl) -> Cons(aux hd, aux tl)
    | Nil as x -> x
    | Lam t -> Lam (aux t)
    | CData _ as x -> x
  in
  let rec add_pis n t =
   if n = 0 then t else App(C.pic,Lam (add_pis (n-1) t),[]) in
  add_pis vars (aux t)

let local_prog { src } =  src

end (* }}} *)
module UnifBits : Indexing = struct (* {{{ *)

  type key = int

  type clause = {
    depth : int;
    args : term list;
    hyps : term list;
    vars : int;
    key : key;
    mode: mode;
  }

  type idx = {
    src : (int * term) list;
    map : (clause * int) list Elpi_ptmap.t  (* timestamp *)
  }

  let key_bits =
    let n = ref 0 in
    let m = ref max_int in
    while !m <> 0 do incr n; m := !m lsr 1; done;
    !n

  let hash x = Hashtbl.hash x * 62653
  let fullones = 1 lsl key_bits -1
  let fullzeros = 0
  let weird = hash min_int
  let abstractionk = 1022   (* TODO *)
  let functor_bits = 9
  let fst_arg_bits = 15
  let max_depth = 1
  let min_slot = 5


  let hd_pred { key } = (- (key land (1 lsl functor_bits - 1)))
  let pp_key hd = C.show (- (hd land (1 lsl functor_bits - 1)))

  let ppclause f { args = args; hyps = hyps; key = hd } =
    Fmt.fprintf f "@[<hov 1>%s %a :- %a.@]" (pp_key hd)
       (pplist (uppterm 0 [] 0 empty_env) "") args
       (pplist (uppterm 0 [] 0 empty_env) ",") hyps

  let dec_to_bin num =
    let rec aux x = 
     if x==1 then "1" else
     if x==0 then "0" else 
     if x mod 2 == 1 then (aux (x/2))^"1"
     else (aux (x/2))^"0"
    in
    let addzero str =
     let s = ref "" in
     for i=1 to (key_bits - (String.length str)) do
      s := "0"^(!s)
     done; 
     !s ^ str
    in
     addzero (aux num)

  let dec_to_bin2 num =
    let rec aux x = 
     if x==1 then "1" else
     if x==0 then "0" else 
     if x mod 2 == 1 then (aux (x/2))^"1"
     else (aux (x/2))^"0"
    in
     aux num

  let key_of ~mode ~depth term =
    let buf = ref 0 in 
    let set_section c k left right =
      let k = abs k in
      let new_bits = (k lsl right) land (fullones lsr (key_bits - left)) in
(*
      Printf.eprintf "%s%s%s %s\n%!" (String.make (key_bits - left) ' ')
                                  (dec_to_bin2 (new_bits lsr right))
                                  (String.make right ' ')
                                  (C.show c);
*)
      (buf := new_bits lor !buf) in
    let rec index lvl tm depth left right =
      [%trace "index" ("@[<hv 0>%a@]"
        (uppterm depth [] 0 empty_env) tm)
      begin match tm with
      | App (k,arg,_) when k == C.asc -> 
         index lvl arg depth left right
      | (App (k,_,_) | Const k) when k == C.uvc -> 
         set_section k weird left right
      | Const k | Custom (k,_) ->
          set_section k (if lvl=0 then k else hash k) left right 
      | Nil ->
          set_section C.nilc (if lvl=0 then C.nilc else hash C.nilc) left right 
      | Cons _ ->
          set_section C.consc (if lvl=0 then C.consc else hash C.consc) left right 
      | UVar ({contents=t},origdepth,args) when t != C.dummy ->
         index lvl (deref_uv ~from:origdepth ~to_:depth args t) depth left right
      | Lam _ -> set_section abstractionk abstractionk left right
      | CData s -> set_section C.(from_stringc "CData") (CData.hash s) left right
      | Arg _ | UVar _ | AppArg _ | AppUVar _ ->
         if mode = `Clause then set_section C.uvc fullones left right
         else set_section C.uvc fullzeros left right
      | App (k,arg,argl) -> 
         let slot = left - right in
         if lvl >= max_depth || slot < min_slot
         then set_section k (if lvl=0 then k else hash k) left right
         else
           let nk, hd, fst_arg, sub_arg =
             if lvl = 0 then
               let sub_slots = List.length argl in
               if sub_slots = 0 then
                 k,functor_bits,slot-functor_bits,0
               else
                 let args_bits = slot - functor_bits - fst_arg_bits in
                 let sub_arg = args_bits / sub_slots in
                 k,functor_bits,fst_arg_bits + args_bits mod sub_slots, sub_arg
             else
               let sub_slots = List.length argl + 2 in
               let sub_arg = slot / sub_slots in
               hash k, sub_arg, sub_arg + slot mod sub_slots, sub_arg  in
           let right_hd = right + hd in
           set_section k nk right_hd right;
           let j = right + hd + fst_arg in
           index (lvl+1) arg depth j right_hd;
           if sub_arg > 0 && j + sub_arg <= left
           then subindex lvl depth j left sub_arg argl
      end]
     and subindex lvl depth j left step = function
       | [] -> ()
       | x::xs ->
          let j2 = j + step in
          index (lvl+1) x depth j2 j;
          if j2 + step <= left then subindex lvl depth j2 left step xs
    in
      index 0 term depth key_bits 0;
(*       Format.eprintf "%s %a\n\n%!" (dec_to_bin !buf) (uppterm 0 [] 0 empty_env) term; *)
      !buf

  let get_clauses ~depth a { map = m } =
    let ind = key_of ~mode:`Query ~depth a in
    let cl_list = List.flatten (Elpi_ptmap.find_unifiables ~functor_bits ind m) in
    [%log "get_clauses" (pp_key ind) (List.length cl_list)];
    List.map fst
      (List.fast_sort (fun (_,cl1) (_,cl2) -> compare cl1 cl2) cl_list)
      
  let timestamp = ref 0

  let add_clauses ?(op=decr) clauses s { map = ptree; src } =
    let map = List.fold_left (fun m clause -> 
      let ind = clause.key in
      let clause = clause, !timestamp in
      op timestamp;
      try 
        let cl_list = Elpi_ptmap.find ind m in
        Elpi_ptmap.add ind (clause::cl_list) m
      with Not_found -> 
        Elpi_ptmap.add ind [clause] m
    ) ptree clauses in
    { map; src = s :: src }
 
  let make_index p =
    timestamp := 1;
    let m = add_clauses ~op:incr p (0,C.cutc) { map = Elpi_ptmap.empty; src = [] } in
    timestamp := 0;
    { m with src = [] }

  (* Get rid of optional arg *)
  let add_clauses cl p pt = add_clauses cl p pt

  (* from (key, (key clause * int) list) list  
    creates  key clause list *)
  let rec flatten_ = function
     [] -> []
   | (_,l)::tl -> (List.map (fun (cl,_) -> cl) l) @ flatten_ tl

let local_prog { src } = src 

end (* }}} *)

(*
open UnifBits
type idx = UnifBits.idx
*)

(* open UnifBits *)
open TwoMapIndexing
type idx = TwoMapIndexing.idx

(* Used to pass the program to the CHR runtime *)
let orig_prolog_program = Fork.new_local (make_index [])

(******************************************************************************
  Dynamic Prolog program
 ******************************************************************************)

module Clausify : sig

  val clausify : int -> constant -> term -> clause list * int
  
  val modes : mode_decl C.Map.t Fork.local_ref

  val lp_list_to_list : term -> term list
  val get_lambda_body : int -> term -> term
  val split_conj : term -> term list

end = struct  (* {{{ *)
let modes = Fork.new_local C.Map.empty

let rec term_map m = function
  | Const x when List.mem_assoc x m -> C.of_dbl (List.assoc x m)
  | Const _ as x -> x
  | App(c,x,xs) when List.mem_assoc c m ->
      App(List.assoc c m,term_map m x, smart_map (term_map m) xs)
  | App(c,x,xs) -> App(c,term_map m x, smart_map (term_map m ) xs)
  | Lam x -> Lam (term_map m x)
  | UVar _ as x -> x
  | AppUVar(r,lvl,xs) -> AppUVar(r,lvl,smart_map (term_map m) xs)
  | Arg _ as x -> x
  | AppArg(i,xs) -> AppArg(i,smart_map (term_map m) xs)
  | Custom(c,xs) -> Custom(c,smart_map (term_map m) xs)
  | Cons(hd,tl) -> Cons(term_map m hd, term_map m tl)
  | Nil as x -> x
  | CData _ as x -> x
let rec split_conj = function
  | App(c, hd, args) when c == C.andc || c == C.andc2 ->
      split_conj hd @ List.(flatten (map split_conj args))
  | f when f == C.truec -> []
  | _ as f -> [ f ]
;;

let rec lp_list_to_list = function
  | Cons(hd, tl) -> hd :: lp_list_to_list tl
  | Nil -> []
  | x -> error (Fmt.sprintf "%s is not a list" (show_term x))
;;

let rec get_lambda_body depth = function
 | UVar ({ contents=g },from,args) when g != C.dummy ->
    get_lambda_body depth (deref_uv ~from ~to_:depth args g)
 | AppUVar ({contents=g},from,args) when g != C.dummy -> 
    get_lambda_body depth (deref_appuv ~from ~to_:depth args g)
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

let clausify vars depth t =
  let rec claux vars depth hyps ts lts lcs t =
  [%trace "clausify" ("%a %d %d %d %d\n%!"
      (ppterm (depth+lts) [] 0 empty_env) t depth lts lcs (List.length ts)) begin
  match t with
    Nil -> [],lts
  | Cons(g1,g2) ->
     let clauses,lts = claux vars depth hyps ts lts lcs g1 in
     let moreclauses,lts = claux vars depth hyps ts lts lcs g2 in
      clauses@moreclauses,lts
  | App(c, g, gs) when c == C.andc || c == C.andc2 ->
     let res = claux vars depth hyps ts lts lcs g in
     List.fold_right
      (fun g (clauses,lts) ->
        let moreclauses,lts = claux vars depth hyps ts lts lcs g in
         clauses@moreclauses,lts
      ) gs res
  | App(c, g2, [g1]) when c == C.rimplc ->
     claux vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == C.rimplc -> assert false
  | App(c, g1, [g2]) when c == C.implc ->
     claux vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == C.implc -> assert false
  | App(c, arg, []) when c == C.sigmac ->
     let b = get_lambda_body (depth+lts) arg in
     let args =
      List.rev (List.filter (function (Arg _) -> true | _ -> false) ts) in
     let cst =
      match args with
         [] -> Const (depth+lcs)
       | hd::rest -> App (depth+lcs,hd,rest) in
     claux vars depth hyps (cst::ts) (lts+1) (lcs+1) b
  | App(c, arg, []) when c == C.pic ->
     let b = get_lambda_body (depth+lts) arg in
     claux (vars+1) depth hyps (Arg(vars,0)::ts) (lts+1) lcs b
  | Const _
  | App _ as g ->
     let hyps =
      List.(flatten (rev_map (fun (ts,g) ->
         let g = hmove ~from:(depth+lts) ~to_:(depth+lts+lcs) g in
         let g = subst depth ts g in
          split_conj g
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
       | Lam _ | Custom _ | CData _ -> assert false
       | UVar _ | AppUVar _ -> assert false
       | Cons _ | Nil -> assert false
     in
     let all_modes =
      let mode =
        try C.Map.find hd !modes
        with Not_found -> Multi [] in
      match mode with
      | Mono [] -> assert false
      | Mono m -> [g,args,hyps,m]
      | Multi l ->
           (g,args,hyps,[]) ::
           List.map (fun (k,subst) ->
             let map = term_map ((hd,k) :: subst) in
             match C.Map.find k !modes with
             | exception Not_found -> assert false
             | Multi _ -> assert false
             (* not smart *)
             | Mono m -> map g, List.map map args, List.map map hyps, m 
         ) l in
      List.map (fun (g,args,hyps,mode) ->
              let c = { depth = depth+lcs ; args= args; hyps = hyps; mode;
          vars = vars; key=key_of ~mode:`Clause ~depth:(depth+lcs) g} in
              [%spy "extra" ppclause c];
              c
          )
       all_modes, lcs
  | UVar ({ contents=g },from,args) when g != C.dummy ->
     claux vars depth hyps ts lts lcs
       (deref_uv ~from ~to_:(depth+lts) args g)
  | AppUVar ({contents=g},from,args) when g != C.dummy -> 
     claux vars depth hyps ts lts lcs
       (deref_appuv ~from ~to_:(depth+lts) args g)
  | Arg _ | AppArg _ -> anomaly "claux called on non-heap term"
  | Lam _ | Custom _ | CData _ ->
     error "Assuming a custom or string or int or float or function"
  | UVar _ | AppUVar _ -> error "Flexible assumption"
  end] in
    claux vars depth [] [] 0 0 t
;;
end (* }}} *) 
open Clausify

(******************************************************************************
  Choice stack
 ******************************************************************************)

(* This has to stay here, we want no Index wrap around idx *)
type goal = (*depth:*)int * idx * term

(* The activation frames points to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. For bad reasons, we call it lvl in the code. *)
type frame =
 | FNil
 | FCons of (*lvl:*)alternative * goal list * frame
and alternative = {
  lvl : alternative;
  program : idx;
  depth : int;
  goal : term;
  goals : goal list;
  stack : frame;
  trail : T.trail;
  custom_constraints : T.custom_constraints;
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

type runtime = {
  search : query -> alternative;
  next_solution : alternative -> alternative;

  (* low level part *)
  destroy : unit -> unit;
  exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  get : 'a. 'a Fork.local_ref -> 'a;
}

         
let do_make_runtime : (?print_constraints:bool -> program -> runtime) ref =
 ref (fun ?print_constraints _ -> anomaly "do_make_runtime not initialized")

module Constraints : sig
    
  val propagation : constraint_def list ref -> (int * idx * term) list
  val resumption : constraint_def list -> (int * idx * term) list

  val chrules : CHR.t Fork.local_ref

  val delay_goal :
    depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit

  (* Like delay_goal, but the context is trimmed according to the clique
   * the constraint lives in *)
  val declare_constraint :
    depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit

  val wrap_prolog_prog : idx -> prolog_prog
  val unwrap_prolog_prog : prolog_prog -> idx

end = struct (* {{{ *)

exception NoMatch

type prolog_prog += Index of idx
let () = extend_printer pp_prolog_prog (fun fmt -> function
  | Index _ -> Fmt.fprintf fmt "<prolog_prog>";`Printed
  | _ -> `Passed)
let wrap_prolog_prog x = Index x
let unwrap_prolog_prog = function Index x -> x | _ -> assert false

type freeze_map = {
  c2uv : (term_attributed_ref * int * term) C.Map.t;
  arg2goal : int IM.t;
}

exception Found of constant * term

(* This is linear, but a ref cannot be sorted nor hashed since it is moved
 * by the Gc *)
let uv2c r { c2uv } =
  try
    C.Map.iter (fun c (r',_,t) -> if r == r' then raise (Found(c,t))) c2uv;
    raise Not_found
  with Found(c, t) -> c, t

let empty_freeze_map = { c2uv = C.Map.empty; arg2goal = IM.empty }

let freeze_uv r lvl ({ c2uv } as fm) =
  try fm, uv2c r fm
  with Not_found ->
    let n, x as nx = C.fresh () in
    [%spy "freeze-add" (fun fmt tt ->
       Fmt.fprintf fmt "%s == %a" (C.show n) (ppterm 0 [] 0 empty_env) tt)
       (UVar (r,lvl,0))];
    { fm with c2uv = C.Map.add n (r,lvl,x) c2uv }, nx

let frozenc2uv p { c2uv } = C.Map.find p c2uv
let frozenc2t p { c2uv } = let _, _, t = C.Map.find p c2uv in t

let is_frozen c m =
   try let _t = frozenc2t c m in true
   with Not_found -> false

let freeze ad m t =
  let m = ref m in
  let freeze_uv r lvl =
    let m', nc = freeze_uv r lvl !m in
    m := m';
    nc in
  let rec freeze ad orig = match orig with
    | UVar( { contents = t} , 0,0) when t != C.dummy -> freeze ad t
    | UVar( { contents = t} , vardepth, args) when t != C.dummy ->
(*                     assert false; *)
        freeze ad (deref_uv ~from:vardepth ~to_:ad args t)
      
    | AppUVar ( { contents = t }, _, _) when t != C.dummy -> assert false
    | UVar( r, lvl, ano) ->
       let n, c = freeze_uv r lvl in
       (match C.mkinterval 0 (lvl+ano) 0 with
       | [] -> c
       | [x] -> App(n,x,[])
       | x::xs -> App(n,x,xs))
    | AppUVar( r, lvl, args ) ->
       let n, c = freeze_uv r lvl in
       let args = freeze_list ad args args in
       (match C.mkinterval 0 lvl 0 @ args with
       | [] -> c
       | [x] -> App(n,x,[])
       | x::xs -> App(n,x,xs))
    | App(c,x,xs) ->
        let x' = freeze ad x in
        let xs' = freeze_list ad xs xs in
        if x == x' && xs == xs' then orig else App(c,x',xs')
    | Const _ -> orig
    | Cons(hd,tl) ->
        let hd' = freeze ad hd in
        let tl' = freeze ad tl in
        if hd == hd' && tl == tl' then orig else Cons(hd',tl')
    | Nil -> orig
    | Arg _ | AppArg _ -> anomaly "freeze ad: not an heap term"
    | Lam t -> let t' = freeze (ad+1) t in if t == t' then orig else Lam t'
    | CData _ -> orig
    | Custom(c,xs) ->
        let xs' = freeze_list ad xs xs in
        if xs == xs' then orig else Custom(c,xs')
  and freeze_list ad l orig =
    match l with
    | [] -> l
    | x :: xs ->
       let xs' = freeze_list ad xs (List.tl orig) in
       let x' = freeze ad x in
       if x == x' && xs == xs' then orig
       else x' :: xs'
  in
  let t = freeze ad t in
  !m, t
;;

let freeze ad m t =
  [%spy "freeze-in"  (ppterm 0 [] 0 empty_env) t];
  let m, t' = freeze ad  m t in
  [%spy "freeze-out"  (ppterm 0 [] 0 empty_env) t'];
  m, t'

let freeze_matched_args goalno e argsdepth m =
  let m, _ =
    Array.fold_left (fun (m,i) ei ->
      (if ei != C.dummy && not (IM.mem i m.arg2goal) then
              (* XXX ugly, arg2goal also used to not-repeat twice the freeze *)
        let m, ei = freeze argsdepth m ei in
        e.(i) <- ei;
        { m with arg2goal = IM.add i goalno m.arg2goal }
      else
        m),i+1)
     (m,0) e in
  m

let match_same_depth_and_freeze goalno e depth m a b =
  [%trace "matching" ("@[<hov>%a ===@ %a@]" (ppterm depth [] 0 e) a (ppterm depth [] 0 e) b) begin
  if unif ~matching:true depth e depth a b
  then freeze_matched_args goalno e depth m
  else raise NoMatch
  end]

let replace_const m t =
  let rec rcaux = function
    | Const c as x -> (try C.of_dbl (List.assoc c m) with Not_found -> x)
    | Lam t -> Lam (rcaux t)
    | App(c,x,xs) ->
        App((try List.assoc c m with Not_found -> c),
            rcaux x, smart_map rcaux xs)
    | Custom(c,xs) -> Custom(c,smart_map rcaux xs)
    | Cons(hd,tl) -> Cons(rcaux hd, rcaux tl)
    | (CData _ | UVar _ | Nil) as x -> x
    | Arg _ | AppArg _ -> assert false
    | AppUVar(r,lvl,args) -> AppUVar(r,lvl,smart_map rcaux args) in
  [%spy "alignement-replace-in" pp_term t];
  let t' = rcaux t in
  [%spy "alignement-replace-out" pp_term t'];
  t'
;;

let ppmap fmt (g,l) =
  let aux fmt (c1,c2) = Fmt.fprintf fmt "%s -> %s" (C.show c1) (C.show c2) in
  Fmt.fprintf fmt "%d = %a" g (pplist aux ",") l
;;

  (* Limited to bijections *)
let align_frozen ({ arg2goal } as m) e alignement ngoals =
  if alignement = [] then () else begin
  [%spy "alignement-alignement" (fun fmt m ->
    Fmt.fprintf fmt "%a%!" (pplist pp_int ";") m) alignement];
  [%spy "alignement-arg2goal" (fun fmt m ->
    Fmt.fprintf fmt "%a%!" (pplist (pp_pair pp_int pp_int) ";") m)
     (IM.bindings arg2goal)];
  if List.length alignement <> List.length (uniq (List.sort compare alignement))
    then error "Alignement with duplicates";
  let kg = List.map (fun i -> i,IM.find i arg2goal) alignement in
  let gs = List.map snd kg in
  [%spy "alignement-gs" (fun fmt m ->
    Fmt.fprintf fmt "%a%!" (pplist pp_int ";") m) gs];
  let uniq_gs = uniq (List.sort compare gs) in
  if List.length gs <> List.length uniq_gs || List.length gs <> ngoals then
    error "Alignement invalid: 1 key per goal";
  let (bkey, bgoal), todo = List.hd kg, List.tl kg in
  (* quick check for same key *)
  let same_k = ref None in
  let mkconstlist l =
    let k, l =
      match l with
      | App(c,arg,args) when is_frozen c m -> Constants.of_dbl c, arg::args
      | Const c as x when is_frozen c m -> x, [] 
        (* XXX In this case we should spread apart all variables,
         * or assert they are never compared/mixed (hard with dependent types *)
      | _ -> Constants.dummy, lp_list_to_list l in
    if !same_k == None then same_k := Some k;
    if option_get !same_k != k then raise NoMatch;
    List.map (function
      | Const x -> x
      | t -> error ("align on non var list: " ^
                    Format.asprintf "%a" (ppterm 0 [] 0 e) t)) l in
  let bkey = mkconstlist e.(bkey) in
  let todo =
    List.map (fun (key, goal) -> goal, bkey, mkconstlist e.(key)) todo in
  let mkmap base tgt =
    if List.length base <> List.length tgt then raise NoMatch else
    List.combine tgt base in
  let maps = List.map (fun (g,base,tgt) -> g,mkmap base tgt) todo in
  [%spy "alignement" (fun fmt m ->
    Fmt.fprintf fmt "%a%!"
      (pplist ppmap ";") m) maps];
  Array.iteri (fun i value ->
    try
      let goal = IM.find i arg2goal in
      if goal <> bgoal then
        let map = List.assoc goal maps in 
        e.(i) <- replace_const map e.(i)
    with Not_found -> ()
  ) e
  end
;;

let thaw max_depth e m t =
  let rec aux = function
  | UVar( { contents = t} , lvl, ano) when t != C.dummy ->
      aux (deref_uv ~from:lvl ~to_:max_depth ano t)
  | AppUVar( { contents = t} , lvl, args) when t != C.dummy ->
      aux (deref_appuv ~from:lvl ~to_:max_depth args t)
  | Arg(i, ano) when e.(i) != C.dummy ->
      aux (deref_uv ~from:max_depth ~to_:max_depth ano e.(i))
  | AppArg(i, args) when e.(i) != C.dummy ->
      aux (deref_appuv ~from:max_depth ~to_:max_depth args e.(i))
  | Arg(i,ano) -> e.(i) <- UVar(oref C.dummy,max_depth,ano); e.(i)
  | AppArg(i,args) ->
      e.(i) <- mkAppUVar (oref C.dummy) max_depth (List.map aux args); e.(i)
  | App(c,x,xs) ->
      (try
        let r, lvl, _ = frozenc2uv c m in
        if List.length xs + 1 >= lvl then
         let _, xs = partition_i (fun i t ->
           if i < lvl then begin
             if t <> Const i then assert false;
             true
           end
             else false) (x::xs) in
         mkAppUVar r lvl  (List.map (aux) xs)
        else
         assert false (* TODO *)
      with Not_found -> 
        App(c,aux x, List.map (aux) xs))
  | Const x as orig ->
     (try
        let r, lvl, _ = frozenc2uv x m in
        if lvl = 0 then
         UVar(r,lvl,0)
        else
         let r' = oref C.dummy in
         (*if not !T.last_call then
          T.trail := (Assignement r) :: !T.trail; ????? *)
         r @:= UVar(r',0,lvl);
         UVar (r', 0, 0)
      with Not_found -> orig)
  | Cons(hd,tl) -> Cons (aux hd, aux tl)
  | Nil as x -> x
  | CData _ as x -> x
  | Custom(c,ts) -> Custom(c,List.map (aux) ts)
  | Lam t -> Lam (aux t)
  | AppUVar(r,lvl,args) -> mkAppUVar r lvl (List.map (aux) args)
  | UVar _ as x -> x
  in
    aux t
;;

let thaw max_depth e m t =
  [%spy "thaw-in"  (ppterm 0 [] 0 e) t];
  let t' = thaw max_depth e m t in
  [%spy "thaw-out"  (ppterm 0 [] 0 e) t'];
  t'

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

(* hmove a term possibly containing Args *)
(* TODO: the function is almost identical to the aux of close_with_pis
   but here we do not instantiate Args. The two codes must be unified *)
let lift_pat ~from ~to_ t =
  let delta = to_ - from in
  let rec aux = function
  | Const n as x ->
     if n < from then x else C.of_dbl (n + delta)
  | Lam r -> Lam (aux r)
  | App (n,x,xs) ->
      App((if n < from then n else n + delta), aux x, List.map aux xs)
  | Cons(hd,tl) -> Cons(aux hd, aux tl)
  | Nil as x -> x
  | Arg _ as x -> x
  | AppArg(i,xs) -> AppArg(i,List.map aux xs)
  | UVar _ as x ->
     (* TODO: quick hack here, but it does not work for AppUVar *)
     hmove ~from ~to_ x
  | AppUVar _ -> assert false
  | Custom(c,xs) -> Custom(c,List.map aux xs)
  | CData _ as x -> x
  in
    aux t
;;

let chrules = Fork.new_local CHR.empty

let delay_goal ?(filter_ctx=fun _ -> true) ~depth prog ~goal:g ~on:keys =
  let pdiff = local_prog prog in
  let pdiff = List.filter filter_ctx pdiff in
  [%spy "delay-goal" (fun fmt x-> Fmt.fprintf fmt
    (*"Delaying goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
    "@[<hov 2> ...@ ⊢^%d %a@]\n%!"
      (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*) depth
      (uppterm depth [] 0 empty_env) x) g];
  let kind = Constraint { depth; prog = Index prog; pdiff; goal = g } in
  CS.declare_new { kind ; blockers = keys }
;;

let rec head_of = function
  | Const x -> x
  | App(x,Lam f,_) when C.(x == pic) -> head_of f
  | App(x,hd,_) when C.(x == rimplc) -> head_of hd
  | App(x,hd,_) when C.(x == andc) -> head_of hd (* FIXME *)
  | App(x,_,_) -> x
  | Custom(x,_) -> x
  | AppUVar(r,_,_)
  | UVar(r,_,_) when !!r != C.dummy -> head_of !!r
  | _ -> anomaly "strange head"

let declare_constraint ~depth prog ~goal:g ~on:keys =
  let clique = CHR.clique_of (head_of g) !chrules in 
  (* XXX head_of is weak because no clausify ??? XXX *)
  delay_goal ~filter_ctx:(fun (_,x) -> C.Set.mem (head_of x) clique)
    ~depth prog ~goal:g ~on:keys
let delay_goal ~depth prog ~goal:g ~on:keys =
  delay_goal ~depth prog ~goal:g ~on:keys


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


(* cstr is a new_delayed constraint, the active one;
   cstr_position is its position, so far, wrt all other constraints
     when matched against chr rules;
   the two lists in output are the constraints to be removed and added *)
let propagate { CS.cstr; cstr_position } history =
 let sequent_of_constr { depth; pdiff = p; goal = t } = depth, p, t in
(*
 let rec find_entails nargs_ref max_depth n = function
   | Lam t -> find_entails nargs_ref max_depth (n+1) t
   | App(c,x,[g]) when c == C.entailsc -> n, x, g
   | t ->
      let i = !nargs_ref in
      incr nargs_ref; 
      n, Arg(i,0), t in
 let sequent_of_pat nargs_ref max_depth ruledepth = function
   | App(c,x,[]) when c == C.nablac ->
       let min_depth, ctx, g = find_entails nargs_ref max_depth ruledepth x in
       (min_depth, ctx, g)
   | Lam _ -> error "syntax error in propagate"
   | x -> 
       let min_depth, ctx, g = find_entails nargs_ref max_depth ruledepth x in
       (min_depth, ctx, g) in
*)
  let sequent_of_pat ruledepth (ctx,goal) = ruledepth,ctx,goal in

 (*Fmt.fprintf Fmt.std_formatter "PROPAGATION %d\n%!" cstr_position;*)
 (* CSC: INVARIANT: propagate clauses can never be assumed using
    implication. Otherwise ~depth:0 is wrong and I do not see any
    reasonable semantics (i.e. a semantics where the scoping is not
    violated). For the same reason I took the propagate clauses from
    the !orig_prolog_program. *)
 let rules =
   let _,_,t = sequent_of_constr cstr in
   let hd = head_of t in
   CHR.rules_for hd !chrules in

 let prolog_program = wrap_prolog_prog !orig_prolog_program in
 let modes = !modes in
 let chr = CHR.(wrap_chr empty) in

 let no_such_j = ref true in

 let result =
    rules |> map_exists (fun ({
        Elpi_ast.to_match = pats_to_match; to_remove = pats_to_remove;
        new_goal; guard = condition; depth = ruledepth; nargs;
        alignement }
      as propagation_rule) ->

              (* XXX To do in compilation phase *)
    let len_pats_to_match = List.length pats_to_match in
    let patsno = len_pats_to_match + List.length pats_to_remove in
    let patterns = pats_to_match @ pats_to_remove in
    if patsno < 1 then
      error "CHR propagation must mention at least one constraint";

    if cstr_position >= patsno then
      (* The active constraint is to be matched in a position that
       * requires a rule with more patterns *)
      None
    else
      (* We put the active constraint inside all permutations of the
       * others, in cstr_position to obtain candidates to be matched
       * with pats_to_match@pats_to_remove *)
      let candidates =
        mk_permutations patsno cstr cstr_position (CS.contents ()) in

     candidates |> map_exists (fun (constraints as orig_constraints) ->
      let hitem = HISTORY.({ propagation_rule; constraints }) in
      no_such_j := false;
      if HISTORY.mem history hitem then begin
(*         Fmt.fprintf Fmt.std_formatter "pruned\n%!" ; *)
        None
        end
      else
       let () = HISTORY.add history hitem () in
       let constraints = List.map sequent_of_constr constraints in

       (* max depth of rule and constraints involved in the matching *)
       let max_depth =
         List.fold_left (fun acc (d,_,_) -> max d acc) ruledepth constraints in

       let constraints_contexts, constraints_goals =
         List.fold_right (fun (d,p,g) (ctxs, gs) ->
           p :: ctxs, (d,g) :: gs)
           constraints ([],[]) in

       let patterns = List.map (sequent_of_pat ruledepth) patterns in

       let e = Array.make nargs C.dummy in

       let patterns_contexts, patterns_goals =
         List.fold_right (fun (d,ctx,g) (ctxs, gs) ->
           if d > max_depth then raise NoMatch;
           (d, ctx) :: ctxs, (d,g) :: gs)
           patterns ([],[]) in
         
       let match_p i m (dt,t) (dp,pat) =
         let t = hmove ~from:dt ~to_:max_depth t in
         let pat = lift_pat ~from:dp ~to_:max_depth pat in
         match_same_depth_and_freeze i e max_depth m t pat in

       let match_ctx i m lt (dp,pctx) =
         let lt = List.map (fun (d,t) -> hmove ~from:d ~to_:max_depth t) lt in
         let t = list_to_lp_list lt in
         let pctx = lift_pat ~from:dp ~to_:max_depth pctx in
         match_same_depth_and_freeze i e max_depth m t pctx in

       let program = { (* runs deep enough to let one use all pi-vars *)
         chr; prolog_program; modes; query_depth = max_depth;
       } in
       let { search; get; exec; destroy } =
         !do_make_runtime  ~print_constraints:false program in
       let check = function
         | None -> ()
         | Some guard -> try
             let _ = search ([],max_depth,e, guard) in
             if get CS.Ugly.delayed <> [] then
               error "propagation rules must not $delay"
           with No_clause -> raise NoMatch in

       let result = try

         (* matching *)
         let m = exec (fun m ->      
           [%spy "propagate-trail" (fun fmt _ -> T.print_trail fmt) ()];
           [%spy "propagate-try-rule"
             (Elpi_ast.pp_chr pp_term C.pp) propagation_rule];
           [%spy "propagate-try-on"
             (pplist (pp_pair pp_int pp_term) ";") constraints_goals];

           let m = fold_left2i match_p m
             constraints_goals patterns_goals in
           let m = fold_left2i match_ctx m
             constraints_contexts patterns_contexts in
           align_frozen m e alignement patsno;
           [%spy "propagate-trail" (fun fmt _ -> T.print_trail fmt) ()];
           T.to_resume := [];
           assert(!T.new_delayed = []);
           m) empty_freeze_map in

         [%spy "propagate-try-rule-guard" (fun fmt () -> Format.fprintf fmt 
             "@[<hov 2>%a@]" (pp_option (uppterm 0 [] 0 e)) condition) ()];

         (* guard *)
         check condition;

         (* result *)
         let _, constraints_to_remove =
           partition_i (fun i _ -> i < len_pats_to_match) orig_constraints in
         match new_goal with
         | None -> Some(constraints_to_remove, [])
         | Some new_goal ->
             let goal = lift_pat ~from:ruledepth ~to_:max_depth new_goal in
             let goal = thaw max_depth e m goal in
             let prog, pdiff, depth = prolog_program, [], max_depth in
             Some(constraints_to_remove, [ { depth; prog; pdiff; goal } ])
       with NoMatch ->
         [%spy "propagate-try-rule-fail" (fun _ _ -> ()) ()];
         None
       in
       destroy ();
       result))
 in
 match result with
 | Some x -> `Matched x
 | None when !no_such_j -> `NoSuchJ
 | _ -> `NoMatch
;;

let incr_generation { CS.cstr; cstr_position } =
  { CS.cstr; cstr_position = cstr_position + 1 }

let resumption to_be_resumed =
  List.map (fun { depth = d; prog = p; goal = g } ->
    let idx = match p with Index p -> p | _ -> assert false in
    [%spy "propagation-resume" (fun fmt _ -> ()) ()];
    d, idx, g)
  (List.rev to_be_resumed)

let propagation to_be_resumed =
  let history = HISTORY.create 17 in
  while !CS.new_delayed <> [] do
    match !CS.new_delayed with
    | [] -> anomaly "Empty list"
    | propagatable :: rest ->
      (match propagate propagatable history with
        | `NoSuchJ -> CS.new_delayed := rest
        | `NoMatch -> CS.new_delayed := incr_generation propagatable :: rest
        | `Matched (to_be_removed,to_be_added) ->
           (*List.iter (function
              (Constraint ((depth,_,_,g)),_) ->
                Fmt.fprintf Fmt.std_formatter
                 "Killing goal: @[<hov 2> ... ⊢^%d %a@]\n%!" depth (uppterm depth [] 0 empty_env) g
            | _ -> ()) to_be_removed ;*)
           List.iter CS.remove_old_constraint to_be_removed ;
           (*List.iter (fun (depth,_,_,g) ->
                Fmt.fprintf Fmt.std_formatter
                 "Additional goal: @[<hov 2> ... ⊢^%d %a@]\n%!" depth (uppterm depth [] 0 empty_env) g)
             to_be_added ;*)
           (*List.iter add_constraint to_be_added*)
           to_be_resumed := to_be_added @ !to_be_resumed )
  done;
  resumption !to_be_resumed

end (* }}} *)

(******************************************************************************
  Main loop = SLD + delay/resumption
 ******************************************************************************)

module Mainloop : sig

  val make_runtime : ?print_constraints:bool -> program -> runtime

  val register_custom : string ->
    (depth:int -> env:term array -> idx -> term list -> term list) ->
      unit

  val is_custom_declared : constant -> bool

end = struct (* {{{ *)

let register_custom, lookup_custom =
 let (customs :
      (* Must either raise No_clause or succeed with the list of new goals *)
      ('a, depth:int -> env:term array -> idx -> term list -> term list)
      Hashtbl.t)
   =
     Hashtbl.create 17 in
 let check s = 
    if s = "" || s.[0] <> '$' then
      anomaly ("Custom predicate name " ^ s ^ " must begin with $");
    let idx = C.from_stringc s in
    if Hashtbl.mem customs idx then
      anomaly ("Duplicate custom predicate name " ^ s);
    idx in
 (fun s f ->
    let idx = check s in
    Hashtbl.add customs idx f),
 Hashtbl.find customs
;;

let is_custom_declared x =
  try let _f = lookup_custom x in true
  with Not_found -> false
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : ?print_constraints:bool -> program -> runtime =

  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     depth >= 0 is the number of variables in the context. *)
  let rec run depth p g gs (next : frame) alts lvl =
    [%trace "run" ("%a" (ppterm depth [] 0 empty_env) g)
 begin match resume_all () with
  None ->
begin Fmt.fprintf Fmt.std_formatter "Undo triggered by goal resumption\n%!";
  [%tcall next_alt alts]
end
 | Some ((ndepth,np,ng)::goals) ->
    [%tcall run ndepth np ng (goals@(depth,p,g)::gs) next alts lvl]
 | Some [] ->
    match g with
    | c when c == C.cutc -> [%tcall cut p gs next alts lvl]
    | App(c, g, gs') when c == C.andc || c == C.andc2 ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    | App(c, g2, [g1]) when c == C.rimplc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, lcs = clausify 0 depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses clauses (depth,g1) p) g2 gs next alts lvl
    | App(c, g1, [g2]) when c == C.implc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, lcs = clausify 0 depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses clauses (depth,g1) p) g2 gs next alts lvl
(*  This stays commented out because it slows down rev18 in a visible way!   *)
(*  | App(c, _, _) when c == implc -> anomaly "Implication must have 2 args" *)
    | App(c, arg, []) when c == C.pic ->
       let f = get_lambda_body depth arg in
       run (depth+1) p f gs next alts lvl
    | App(c, arg, []) when c == C.sigmac ->
       let f = get_lambda_body depth arg in
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
    | Cons _ | Nil | Lam _ | CData _ -> type_error "Not a predicate"
    | UVar _ | AppUVar _ -> error "Flexible predicate"
    | Custom(c, args) ->
       let f = try lookup_custom c with Not_found -> anomaly"no such custom" in
       match f depth empty_env p args with
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
          pplist ~max:1 ~boxed:true ppclause "|" fmt l)
      begin match l with
      | [] -> [%tcall next_alt alts]
      | c :: cs ->
        let old_trail = !T.trail in
        T.last_call := maybe_last_call && cs = [];
        let env = Array.make c.vars C.dummy in
        match
         for_all3b (fun x y b -> unif ~matching:b depth env c.depth x y)
           args_of_g c.args c.mode false
        with
        | false -> T.undo old_trail (); [%tcall select cs]
        | true ->
           let oldalts = alts in
           let alts = if cs = [] then alts else
             { program = p; depth = depth; goal = g; goals = gs; stack = next;
               trail = old_trail; custom_constraints = !CS.custom_constraints;
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
    if alts == noalts then T.trail := !T.empty_trail;
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
     | { kind = Unification { adepth; bdepth; env; a; b } } as dg :: rest ->
         CS.remove_old dg;
         CS.to_resume := rest;
         (*Fmt.fprintf Fmt.std_formatter
          "Resuming @[<hov 2>^%d:%a@ == ^%d:%a@]\n%!"
           ad (uppterm ad [] 0 empty_env) a
           bd (uppterm ad [] ad e) b;*)
         ok := unif adepth env bdepth a b
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
     if !CS.new_delayed <> [] then Some (Constraints.propagation to_be_resumed)
     else Some (Constraints.resumption !to_be_resumed)
   else None

  and next_alt alts =
   if alts == noalts then raise No_clause
   else
    let { program = p; clauses = clauses; goal = g; goals = gs; stack = next;
          trail = old_trail; custom_constraints = old_constraints;
          depth = depth; lvl = lvl; next = alts} = alts in
    T.undo ~old_trail ~old_constraints ();
    backchain depth p g gs clauses next alts lvl (* XXX *)
  in


 (* Finally the runtime *)
 fun ?(print_constraints=true)
     { query_depth = d; prolog_program = prog; chr; modes = mds } ->
  let { Fork.exec = exec ; get = get ; set = set } = Fork.fork () in
  let depth = ref 0 in (* Initial depth, i.e. number of locals *)
  let chr = CHR.unwrap_chr chr in
  let prog = Constraints.unwrap_prolog_prog prog in
  set orig_prolog_program prog;
  set Constraints.chrules chr;
  set modes mds;
  set T.empty_trail [];
  set T.trail !T.empty_trail;
  set T.last_call false;
  set CS.new_delayed [];
  set CS.to_resume [];
  set CS.Ugly.delayed [];
  depth := d;
  let pr_constraints () =
    if print_constraints then begin
    Fmt.fprintf Fmt.std_formatter "===== delayed ======\n%!";
    CS.print Fmt.std_formatter;
    Fmt.fprintf Fmt.std_formatter "====================\n%!"; end
    in
  let search = exec (fun (_,adepth,q_env,q) ->
     let q = move ~adepth ~depth:adepth ~from:adepth ~to_:adepth q_env q in
     [%spy "run-trail" (fun fmt _ -> T.print_trail fmt) ()];
     T.empty_trail := !T.trail;
     let alts = run !depth !orig_prolog_program q [] FNil noalts noalts in
     pr_constraints ();
     alts) in
  let next_solution = exec (fun alts -> 
     let alts = next_alt alts in
     pr_constraints ();
     alts) in
  let destroy () = exec (fun () -> T.undo ~old_trail:[] ()) () in
  { search; next_solution; exec; get; destroy }
;;

do_make_runtime := make_runtime;;

end (* }}} *)
open Mainloop

(******************************************************************************
  "Compiler" from AST to program
 ******************************************************************************)

let typecheck = ref (fun clauses types -> ())

module Compiler : sig

  val program_of_ast : ?print:[`Yes|`Raw] -> Elpi_ast.decl list -> program
  val query_of_ast : program -> Elpi_ast.term -> query
  val term_of_ast : depth:int -> Elpi_ast.term -> term

  val query_of_ast_cmap :
    int ->
    cmap:term F.Map.t ->
    macro:Elpi_ast.term F.Map.t ->
    types:(term * int * term) list ->
    Elpi_ast.term -> string list * int * term array * term

end = struct (* {{{ *)

module SM = Map.Make(String)

(* To assign Arg (i.e. stack) slots to unif variables in clauses *)
type argmap = {
  lvl : int; (* cross call assertion: all args live in the same lvl *)
  max_arg : int;
  name2arg : (term * int) SM.t;       (* "X" -> Const "%Arg4", 4 *)
  argc2name : (string * int) C.Map.t; (* "%Arg4" -> "X", 4 *)
   (* constant used for symbolic pre-computation, real Arg number *)
}

let empty_amap lvl = { lvl; max_arg = 0; name2arg = SM.empty; argc2name = C.Map.empty }

let stack_arg_of_ast cur_lvl ({ lvl; max_arg = f; name2arg = l } as amap) n =
 assert(lvl = cur_lvl);
 try amap, fst (SM.find n l)
 with Not_found ->
  let cname = Printf.(sprintf "%%Arg%d" f) in
  let n' = C.(from_string cname) in
  let nc = C.(from_stringc cname) in
  { lvl; max_arg = f+1 ;
    name2arg = SM.add n (n',f) l;
    argc2name = C.Map.add nc (n,f) amap.argc2name }, n'
;;

let is_uvar_name f = 
   let c = (F.show f).[0] in
   ('A' <= c && c <= 'Z') || c = '_'
;;

let is_macro_name f = 
   let c = (F.show f).[0] in
   c = '@'
;;

let desugar inner s args =
  let open Elpi_ast in
  let open Func in
  let varname = function Const x -> x | _ -> assert false in
  let last_is_arrow l =
    match List.rev l with
    | App(Const f,[_]) :: _ -> equal f arrowf
    | _ -> false in  
  let chop_last_app l =
    match List.rev l with
    | App(_,[x]) :: xs -> x, List.rev xs
    | _ -> assert false in
  match args with
  | [var;App(Const f,args)] when equal s letf -> f, (args @ [var]) 
  | [var;Const f] when equal s letf -> f, [var] 
  | [App(hd,args); hyps] when equal s rimplf && last_is_arrow args ->
    let res, args = chop_last_app args in
    let var = if inner then mkFreshName () else mkFreshUVar () in
    let args = [App(hd, args @ [var]) ;
                App(Const andf, [App(Const eqf, [var;res]); hyps])] in
    if inner then pif, [Lam(varname var, App(Const s, args ))]
    else s, args
  | args when not (equal s rimplf) && last_is_arrow args ->
    let res, args = chop_last_app args in
    let var = if inner then mkFreshName () else mkFreshUVar () in
    let args = [App(Const s, args @ [var]) ; App(Const eqf, [var;res])] in
    if inner then pif, [Lam(varname var, App(Const rimplf, args))]
    else rimplf, args
  | _ -> s, args
;;
      
let stack_term_of_ast lvl amap cmap macro types ast =
  let module A = Elpi_ast in

  (* This sucks: types and mode declarations should be merged XXX *)    
  let arity t =
    let (c,ct), args =
      match t with
      | A.App (A.Const f,args) -> C.funct_of_ast f, args
      | A.App (A.Custom f,args) -> C.funct_of_ast f, args
      | A.Const c -> C.funct_of_ast c, []
      | A.Custom c -> C.funct_of_ast c, []
      | _ -> error ("only applications can be spilled: " ^ A.show_term t) in
    let nargs = List.length args in
    let missing_args =
      try
        let _,_,ty = List.find (fun (t,_,_) -> t == ct) types in
        let rec napp = function App(_,_,[x]) -> 1 + napp x | _ -> 0 in
        napp ty - nargs 
      with Not_found ->
        match C.Map.find c !modes with
        | Mono l ->
            let arity = List.length l in
            let missing = arity - nargs in
            let output_suffix =
              let rec aux = function false :: l -> 1 + aux l | _ -> 0 in
              aux (List.rev l) in
            if missing > output_suffix then
              error Printf.(sprintf
              "cannot spill %s: only %d out of %d missing arguments are outputs"
              (A.show_term t) output_suffix missing);
            missing
        | Multi _ -> error ("cannot spill multi mode relation " ^ C.show c)
        | exception Not_found ->
           error ("cannot spill, unknown arity of " ^ C.show c) in
    if missing_args <= 0 then
      error ("cannot spill fully applied " ^ A.show_term t);
    missing_args in

  let rec stack_macro_of_ast inner lvl amap cmap f =
    try aux inner lvl amap cmap (F.Map.find f macro)
    with Not_found -> error ("Undeclared macro " ^ F.show f) 
  
  and stack_funct_of_ast inner curlvl amap cmap f =
    try amap, F.Map.find f cmap
    with Not_found ->
     if is_uvar_name f then
       stack_arg_of_ast lvl amap (F.show f)
     else if is_macro_name f then
       stack_macro_of_ast inner curlvl amap cmap f
     else amap, snd (C.funct_of_ast f)

  and stack_custom_of_ast f =
    let cname = fst (C.funct_of_ast f) in
    if not (is_custom_declared cname) then error("No custom named "^F.show f);
    cname
  
  and aux inner lvl amap cmap = function
    | A.Const f when F.(equal f nilf) -> amap, Nil
    | A.Const f -> stack_funct_of_ast inner lvl amap cmap f
    | A.Custom f ->
       let cname = stack_custom_of_ast f in
       amap, Custom (cname, [])
    | A.App(A.Const f, [hd;tl]) when F.(equal f consf) ->
           let amap, hd = aux true lvl amap cmap hd in
           let amap, tl = aux true lvl amap cmap tl in
           amap, Cons(hd,tl)
    | A.App(A.Const f, tl) ->
       let f, tl = desugar inner f tl in
       let amap, rev_tl =
         List.fold_left (fun (amap, tl) t ->
           let amap, t = aux true lvl amap cmap t in
           (amap, t::tl))
          (amap, []) tl in
       let tl = List.rev rev_tl in
       let amap, c = stack_funct_of_ast inner lvl amap cmap f in
       begin match c with
       | Const c -> begin match tl with
          | hd2::tl -> amap, App(c,hd2,tl)
          | _ -> anomaly "Application node with no arguments" end
       | Lam _ -> (* macro with args *)
          amap, deref_appuv ~from:lvl ~to_:lvl tl c
       | _ -> error "Clause shape unsupported" end
    | A.App (A.Custom f,tl) ->
       let cname = stack_custom_of_ast f in
       let amap, rev_tl =
         List.fold_left (fun (amap, tl) t ->
            let amap, t = aux true lvl amap cmap t in
            (amap, t::tl))
          (amap, []) tl in
       amap, Custom(cname, List.rev rev_tl)
    | A.Lam (x,t) when A.Func.(equal x dummyname)->
       let amap, t' = aux true (lvl+1) amap cmap t in
       amap, Lam t'
    | A.Lam (x,t) ->
       let cmap' = F.Map.add x (C.of_dbl lvl) cmap in
       let amap, t' = aux true (lvl+1) amap cmap' t in
       amap, Lam t'
    | A.App (A.App (f,l1),l2) ->
       aux inner lvl amap cmap (A.App (f, l1@l2))
    | A.String str -> amap, CData (in_string str)
    | A.Int i -> amap, CData (in_int i)
    | A.Float f -> amap, CData (in_float f)
    | A.App (A.Lam _,_) -> error "Beta-redexes not in our language"
    | A.App (A.String _,_) -> type_error "Applied string value"
    | A.App (A.Int _,_) -> type_error "Applied integer value"
    | A.App (A.Float _,_) -> type_error "Applied float value"
  in
  let spill ast =
    let spilled_name = ref 0 in
    let rec mkSpilledNames n =
      if n == 0 then []
      else begin
        incr spilled_name;
        let name = F.from_string ("Spilled_" ^ string_of_int !spilled_name) in
        name :: mkSpilledNames (n-1)
      end in
    let add_spilled sp t =
      match sp with
      | [] -> [], [t]
      | _ ->
          let to_spill = map_filter snd sp in
          List.map (fun (x,_) -> x, None) sp,
          [A.(App(Const F.andf, to_spill @ [t]))] in
    let rec mapflat2 f l =
      let l1, l2 = List.(split (map f l)) in
      List.flatten l1, List.flatten l2 in
    let rec aux toplevel = function
      | A.App(A.Const c,fcall :: rest) when F.(equal c spillf) ->
         let ns = mkSpilledNames (arity fcall) in
         let fspills, fcall = aux false fcall in
         assert(List.length fcall = 1);
         let fcall = List.hd fcall in
         let spills, args = mapflat2 (aux false) rest in
         let args = List.map (fun x -> A.Const x) ns in
         fspills @ spills @ [ns,Some (A.mkApp (fcall :: args))], args
      | A.App(A.Const c, args)
         when F.(List.exists (equal c) [andf;andf2;orf;rimplf]) ->
         let spills, args = mapflat2 (aux true) args in
         assert(map_filter snd spills = []);
         spills, [A.App(A.Const c, args)]
      | A.App(A.Const c, [A.Lam (n,arg)])
         when F.(List.exists (equal c) [pif;sigmaf]) ->
         let spills, arg = aux true arg in
         assert(List.length arg = 1);
         let arg = List.hd arg in
         assert(map_filter snd spills = []);
         let arg = List.fold_left (fun acc (ns,_) ->
           List.fold_left (fun acc n ->
            A.(App(Const F.sigmaf, [Lam (n, acc)]))) acc ns) arg spills in
         [], [A.App(A.Const c, [A.Lam (n,arg)])]
      | A.App(A.Const c, args)
         when F.(List.exists (equal c) [implf;rimplf]) ->
         let spills, args = mapflat2 (aux true) args in
         assert(map_filter snd spills = []);
         spills, [A.App(A.Const c, args)]
      | A.App(c,args) ->
         let spills, args = mapflat2 (aux false) args in
         if toplevel then add_spilled spills (A.App(c, args))
         else spills, [A.App(c,args)]
      | (A.String _|A.Float _|A.Int _|A.Const _|A.Custom _) as x -> [], [x]
      | A.Lam(x,t) ->
         let sp, t = aux false t in
         if sp <> [] then error "Not supported yet (spill lambda)";
         assert(List.length t = 1);
         let t = List.hd t in
         [], [A.Lam (x,t)]
    in
      let sp, t = aux true ast in
      assert(List.length t = 1);
      let t = List.hd t in
      assert(map_filter snd sp = []); t in
  let arg_cst amap c args =
    if C.Map.mem c amap then
      let _, argno = C.Map.find c amap in
      mkAppArg argno lvl args
    else if args = [] then C.of_dbl c
    else App(c,List.hd args,List.tl args) in
  let rec argify amap = function
    | Const c -> arg_cst amap c []
    | App(c,x,xs) -> arg_cst amap c (List.map (argify amap) (x::xs))
    | Lam t -> Lam(argify amap t)
    | CData _ as x -> x
    | Custom(c,xs) -> Custom(c,List.map (argify amap) xs)
    | UVar _ | AppUVar _ | Arg _ | AppArg _ -> assert false
    | Nil as x -> x
    | Cons(x,xs) -> Cons(argify amap x,argify amap xs) in
  let spilled_ast = spill ast in
  let amap, term_no_args = aux false lvl amap cmap spilled_ast in
  amap, argify amap.argc2name term_no_args
;;

(* BUG: I pass the empty amap, that is plainly wrong.
   Therefore the function only works on meta-closed terms. *)
let term_of_ast ~depth t =
 let argsdepth = depth in
 let freevars = C.mkinterval 0 depth 0 in
 let cmap =
  List.fold_left (fun cmap i ->
   F.Map.add (F.from_string (C.show (destConst i))) i cmap
   ) F.Map.empty freevars in
 let { max_arg = max }, t =
   stack_term_of_ast depth (empty_amap depth) cmap F.Map.empty [] t in
 let env = Array.make max C.dummy in
 move ~adepth:argsdepth ~from:depth ~to_:depth env t
;;

let query_of_ast_cmap lcs ~cmap ~macro ~types t =
  let { max_arg = max; name2arg = l }, t =
    stack_term_of_ast lcs (empty_amap lcs) cmap macro types t in
  let l = SM.bindings l in
  let l = List.sort (fun (_,(_,x)) (_,(_,y)) -> compare x y) l in
  List.map fst l, 0, Array.make max C.dummy, t
;;

let query_of_ast { query_depth = lcs } t =
  query_of_ast_cmap lcs ~cmap:F.Map.empty ~macro:F.Map.empty ~types:[] t
;;

let chr_of_ast depth cmap macro r =
  let open Elpi_ast in
  let amap = empty_amap depth in
  let intern amap t = stack_term_of_ast depth amap cmap macro [] t in
  let intern2 amap (t1,t2) =
    let amap, t1 = intern amap t1 in
    let amap, t2 = intern amap t2 in
    amap, (t1,t2) in
  let internArg { name2arg } f =
    match SM.find (F.show f) name2arg with
    | (_, n) -> n
    | exception Not_found -> error "alignement on a non Arg" in
  let amap, to_match = map_acc intern2 amap r.to_match in
  let amap, to_remove = map_acc intern2 amap r.to_remove in
  let amap, guard = option_mapacc intern amap r.guard in
  let amap, new_goal = option_mapacc intern amap r.new_goal in
  let alignement = List.map (internArg amap) r.alignement in
  let nargs = amap.max_arg in
  { to_match; to_remove; guard; new_goal; alignement; depth; nargs }

type temp = {
  block : (Elpi_ast.term F.Map.t * Elpi_ast.clause) list;
  cmap : term F.Map.t;
  macro : Elpi_ast.term F.Map.t;
}
type comp_state = {
  program : (CData.t(*loc*) * string list * clause) list;
  lcs : int;
  chr : CHR.t;

  tmp : temp;

  (* nesting *)
  clique : CHR.clique option;  
  ctx : temp list;

  (* metadata *)
  types : (term * int * term) list;
}

let sort_insertion l =
  let rec insert loc name c = function
    | [] -> error ("no clause named " ^ name)
    | (_,{ Elpi_ast.id = Some n }) as x :: xs when n = name ->
         if loc = `Before then c :: x :: xs
         else x :: c :: xs
    | x :: xs -> x :: insert loc name c xs in
  let rec aux acc = function
    | [] -> acc
    | (_,{ Elpi_ast.insert = Some (loc,name) }) as x :: xs ->
          aux (insert loc name x acc) xs
    | x :: xs -> aux (acc @ [x]) xs
  in
  aux [] l
;;

let program_of_ast ?print (p : Elpi_ast.decl list) : program =
 let clausify_block program block lcs cmap types =
   let l = sort_insertion block in
   let clauses, lcs =
     List.fold_left (fun (clauses,lcs) (macro,{ Elpi_ast.body; loc }) ->
      let names,_,env,t = query_of_ast_cmap lcs ~cmap ~macro ~types body in
      if print = Some `Yes then Fmt.eprintf "%a.@;" (uppterm 0 names 0 env) t;
      if print = Some `Raw then Fmt.eprintf "%a.@;" pp_term t;
      let moreclauses, morelcs = clausify (Array.length env) lcs t in
      let loc = in_loc loc in
      clauses @ List.(map (fun x -> loc,names,x) (rev moreclauses)), lcs + morelcs
     ) ([],lcs) l in
   program @ clauses, lcs
 in
 let clauses, lcs, chr, types =
   let rec aux ({ program; lcs; chr; clique; types;
                  tmp = ({ block; cmap; macro } as tmp); ctx } as cs) = function
   | [] ->
       if ctx <> [] then error "Begin without an End";
       let program, lcs = clausify_block program block lcs cmap types in
       program, lcs, chr, cs.types

   | d :: todo ->
      match d with
      | Elpi_ast.Chr r ->
          let clique =
            match clique with
            | None -> error "CH rules allowed only in constraint block"
            | Some c -> c in
          let rule = chr_of_ast lcs cmap macro r in
          let chr = CHR.add_rule clique rule chr in
          aux { cs with chr } todo
      | Elpi_ast.Type(name,typ) ->  (* Check ARITY against MODE *)
          let _, name = C.funct_of_ast name in
          let _,_,env,typ = query_of_ast_cmap lcs ~cmap ~macro ~types typ in
          aux { cs with types = (name,Array.length env,typ) :: types } todo
      | Elpi_ast.Clause c ->
          aux { cs with tmp = { tmp with block = (block @ [macro,c])} } todo
      | Elpi_ast.Begin ->
          aux { cs with tmp = { tmp with block = [] }; ctx = tmp :: ctx } todo
      | Elpi_ast.Accumulated p ->
         aux cs (p @ todo)
      | Elpi_ast.End ->
         if ctx = [] then error "End without a Begin";
         let program, lcs = clausify_block program block lcs cmap types in
         let tmp = List.hd ctx in
         let ctx = List.tl ctx in
         aux { cs with program; tmp; ctx; lcs; clique = None } todo
      | Elpi_ast.Local v ->
         aux {cs with lcs = lcs + 1;
              tmp = { tmp with cmap = F.Map.add v (C.of_dbl lcs) cmap }} todo
      | Elpi_ast.Macro(n, body) ->
         aux { cs with tmp = { tmp with macro = F.Map.add n body macro }} todo
      | Elpi_ast.Mode m -> (* Check ARITY against TYPE *)
           let funct_of_ast c =
             try
               match F.Map.find c cmap with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (C.funct_of_ast c) in
           List.iter (fun (c,l,alias) ->
            let key = funct_of_ast c in
            let mode = l in
            let alias = option_map (fun (x,s) ->
              funct_of_ast x,
              List.map (fun (x,y) -> funct_of_ast x, funct_of_ast y) s) alias
            in
            match alias with
            | None -> modes := C.Map.add key (Mono mode) !modes
            | Some (a,subst) ->
                 modes := C.Map.add a (Mono mode) !modes;
                 match C.Map.find key !modes with
                 | Mono _ -> assert false
                 | Multi l ->
                     modes := C.Map.add key (Multi ((a,subst)::l)) !modes
                 | exception Not_found ->
                     modes := C.Map.add key (Multi [a,subst]) !modes
           ) m;
           aux cs todo
      | Elpi_ast.Constraint fl ->
           let funct_of_ast c =
             try
               match F.Map.find c cmap with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (C.funct_of_ast c) in
          if clique <> None then error "nested constraint";
          let fl = List.map (fun x -> funct_of_ast x) fl in
          let chr, clique = CHR.new_clique fl chr in
          aux { cs with chr; clique = Some clique;
                        tmp = { block = []; cmap; macro };
                        ctx = { block; cmap; macro } :: ctx } todo
   in
     aux { program = []; lcs = 0; chr = CHR.empty; clique = None;
           tmp = { block = []; cmap = F.Map.empty; macro = F.Map.empty };
           ctx = []; types = [] }
         p
 in
 !typecheck clauses types;
 let clauses = List.map (fun (_,_,x) -> x) clauses in
 { query_depth = lcs;
   prolog_program = Constraints.wrap_prolog_prog (make_index clauses);
   chr = CHR.wrap_chr chr;
   modes = !modes}
;;

end (* }}} *)

(******************************************************************************
  API
 ******************************************************************************)

let execute_once program q =
 let { search; destroy } = make_runtime ~print_constraints:true program in
 try ignore (search q) ; destroy (); false
 with No_clause (*| Non_linear*) -> destroy (); true
;;


let mkQApp =
  let appc = C.from_stringc "elpi_app" in
  fun l -> App(appc,list_to_lp_list l,[])

let quote_term ?(app=true) vars term =
  let lamc = C.from_stringc "elpi_lam" in
  let cdatac = C.from_stringc "elpi_cdata" in
  let reloc n = if n < 0 then n else n + vars in
  let rec aux depth = function
    | Const n -> C.of_dbl (reloc n)
    | Lam x -> App(lamc,Lam (aux (depth+1) x),[])
    | App(c,Lam f,[]) when c == C.pic || c == C.sigmac ->
        App(c,Lam (aux (depth+1) f), [])
    | App(c,f,[]) when c == C.pic || c == C.sigmac ->
        App(c,aux depth f, [])
    | App(c,s,[t]) when c == C.arrowc -> App(c,aux depth s,[aux depth t])
    | App(hd,x,xs) when not app ->
        App(reloc hd, aux depth x, List.map (aux depth) xs)
    | App(hd,x,xs) ->
        mkQApp (C.of_dbl (reloc hd) :: List.map (aux depth) (x::xs))
    | Arg(id,0) -> C.of_dbl id
    | Arg(id,argno) -> mkQApp (C.of_dbl id :: C.mkinterval vars argno 0)
    | AppArg(id,xs) -> mkQApp (C.of_dbl id :: List.map (aux depth) xs)
    | UVar ({ contents = g }, from, args) when g != C.dummy ->
       aux depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != C.dummy ->
       aux depth (deref_appuv ~from ~to_:depth args t)
    | UVar _ | AppUVar _ -> assert false
    | Custom(c,[]) -> C.of_dbl c
    | Custom(c,args) ->
        mkQApp (C.of_dbl (reloc c) :: List.map (aux depth) args)
    | CData _ as x -> App(cdatac,x,[])
    | Cons(hd,tl) -> mkQApp [C.cons; aux depth hd; aux depth tl]
    | Nil -> C.nil
  in
    aux vars term

    (* FIXME : close_with_pis already exists but unused *)
let rec piclose t = function
  | 0 -> t
  | n -> App(C.pic,Lam (piclose t (n-1)),[])

let quote_clause (loc, names, { key; args; hyps; vars }) =
  (* horrible hack *)
  let hdc, hd = C.funct_of_ast (F.from_string (pp_key key)) in
  let head = match args with
    | [] -> hd
    | x::xs -> App(hdc,x,xs) in
  let t =
    if hyps = [] then quote_term vars head
    else
      mkQApp [C.rimpl;
              quote_term vars head;
              mkQApp (C.andt :: List.map (quote_term vars) hyps)]
  in
  let names = List.map (fun x -> CData(in_string (F.from_string x))) names in
  App(C.andc,CData loc,[list_to_lp_list names;piclose t vars])
;;

let enable_typechecking () =
  let checker = Compiler.program_of_ast
    (Elpi_parser.parse_program ~paths:[] ~filenames:["elpi_typechecker.elpi"]) in
  typecheck := (fun clauses types ->
    let clist = list_to_lp_list (List.map quote_clause clauses) in
    let tlist = list_to_lp_list (List.map (fun (name,n,typ) ->
        App(C.from_stringc "`:",name,[piclose (quote_term ~app:false 0 typ) n]))
      types) in
    let query =
      let c = C.from_stringc "typecheck-program" in
      [], 0, [||], App(c,clist,[tlist]) in
    if execute_once checker query then
      Printf.eprintf "Anomaly: Type checking aborts\n%!";
    )
;;

let execute_loop program ((q_names,q_argsdepth,q_env,q) as qq) =
 let { search; next_solution } = make_runtime ~print_constraints:true program in
 let k = ref noalts in
 let do_with_infos f x =
  let time0 = Unix.gettimeofday() in
  f x ;
  let time1 = Unix.gettimeofday() in
  prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
 (* Fmt.eprintf "Raw Result: %a\n%!"
    (ppterm depth q_names q_argsdepth q_env) q ;*)
  Fmt.eprintf "Result: \n%!" ;
  List.iteri (fun i name -> Fmt.eprintf "@[<hov 1>%s=%a@]\n%!" name
   (uppterm program.query_depth q_names 0 q_env) q_env.(i)) q_names;
  Fmt.eprintf "Raw result: \n%!" ;
  List.iteri (fun i name -> Fmt.eprintf "@[<hov 1>%s=%a@]\n%!" name
   (ppterm program.query_depth q_names 0 q_env) q_env.(i)) q_names;
  in
 do_with_infos (fun x -> k := search x) qq;
 while !k != noalts do
   prerr_endline "More? (Y/n)";
   if read_line() = "n" then k := noalts else
    try do_with_infos (fun _ -> k := next_solution !k) ()
    with No_clause -> prerr_endline "Fail"; k := noalts
 done
;;

let delay_goal = Constraints.delay_goal
let declare_constraint = Constraints.declare_constraint
let print_delayed () = CS.print Fmt.std_formatter
let is_flex = HO.is_flex
let deref_uv = HO.deref_uv
let deref_appuv = HO.deref_appuv
let register_custom = Mainloop.register_custom
let make_runtime = Mainloop.make_runtime
let program_of_ast = Compiler.program_of_ast
let query_of_ast = Compiler.query_of_ast
let query_of_ast_cmap lvl cmap = Compiler.query_of_ast_cmap lvl ~cmap ~macro:F.Map.empty ~types:[]
let term_of_ast = Compiler.term_of_ast
let lp_list_to_list = Clausify.lp_list_to_list
let split_conj = Clausify.split_conj
let llam_unify ad e bd a b = HO.unif ad e bd a b
module CustomConstraints = CS.Custom

(* vim: set foldmethod=marker: *)
