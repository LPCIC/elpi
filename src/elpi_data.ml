(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* Internal term representation *)

module Fmt = Format
module F = Elpi_ast.Func
open Elpi_util

module IM = IntMap

(******************************************************************************
  Terms: data type definition and printing
 ******************************************************************************)

(* To break circularity, we open the index type (index of clauses) here
 * and extend it with the Index constructor when such data type will be
 * defined.  The same for chr with CHR.t *)
type prolog_prog = ..
let pp_prolog_prog = mk_extensible_printer ()

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
  (* Misc: custom predicates, ... *)
  | Custom of constant * term list
  | CData of CData.t
  (* Optimizations *)
  | Cons of term * term
  | Nil
  | Discard
and term_attributed_ref = {
  mutable contents : term [@printer (pp_extensible_any ~id:id_term pp_oref)];
  mutable rest : stuck_goal list [@printer fun _ _ -> ()]
                                 [@equal fun _ _ -> true];
}
and stuck_goal = {
  mutable blockers : blockers;
  kind : stuck_goal_kind;
}
and blockers = term_attributed_ref list
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
  cdepth : int;
  prog : prolog_prog [@equal fun _ _ -> true]
               [@printer (pp_extensible pp_prolog_prog)];
  context : clause_src list;
  conclusion : term;
}
and clause_src = { hdepth : int; hsrc : term }
[@@deriving show, eq]

module C = struct

  let { CData.cin = in_int; isc = is_int; cout = out_int } as int =
    Elpi_ast.cint
  let is_int = is_int
  let to_int = out_int
  let of_int x = CData (in_int x)

  let { CData.cin = in_float; isc = is_float; cout = out_float } as float =
    Elpi_ast.cfloat
  let is_float = is_float
  let to_float = out_float
  let of_float x = CData (in_float x)
  
  let { CData.cin = in_string; isc = is_string; cout = out_string } as string =
    Elpi_ast.cstring
  let is_string = is_string
  let to_string x = out_string x
  let of_string x = CData (in_string x)

end

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
  val cutc     : constant
  val truec    : term
  val andc     : constant
  val andt     : term
  val andc2    : constant
  val orc      : constant
  val implc    : constant
  val rimplc   : constant
  val rimpl    : term
  val pic      : constant
  val pi       : term
  val sigmac   : constant
  val eqc      : constant
  val rulec    : constant
  val cons     : term
  val consc    : constant
  val nil      : term
  val nilc     : constant
  val entailsc : constant
  val nablac   : constant
  val uvc      : constant
  val asc      : constant
  val arrowc   : constant
  val frozenc  : constant

  val ctypec   : constant

  val spillc   : constant

  val declare_constraintc : constant
  val print_constraintsc  : constant
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
   let xx = Const n in
   Hashtbl.add h' n ("frozen-"^string_of_int n);
   Hashtbl.add h'' n xx;
   n,xx)
;;

let pp fmt c = Format.fprintf fmt "%s" (show c)

let from_stringc s = fst (funct_of_ast F.(from_string s))
let from_string s = snd (funct_of_ast F.(from_string s))

let cutc, cut = funct_of_ast F.cutf
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
let spillc = fst (funct_of_ast (F.spillf))
let arrowc = fst (funct_of_ast F.arrowf)
let frozenc = fst (funct_of_ast (F.from_string "uvar"))
let ctypec = fst (funct_of_ast F.ctypef)

let declare_constraintc = from_stringc "declare_constraint"
let print_constraintsc = from_stringc "print_constraints"

let dummy = App (-9999,cut,[])

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

module CHR : sig

  (* a set of rules *)
  type t

  (* a set of predicates contributing to represent a constraint *)
  type clique 

  type sequent = { eigen : term; context : term; conclusion : term }
  and alignment = { arg2sequent : int IM.t; keys : (string * int) list }
  and rule = {
    to_match : sequent list;
    to_remove : sequent list;
    alignment : alignment option;
    guard : term option;
    new_goal : sequent option;
    nargs : int [@default 0];
    pattern : Constants.t list;
  }
  val pp_sequent : Format.formatter -> sequent -> unit
  val show_sequent : sequent -> string
  val pp_rule : Format.formatter -> rule -> unit
  val show_rule : rule -> string

  val empty : t

  val new_clique : constant list -> t -> t * clique
  val clique_of : constant -> t -> Constants.Set.t option
  val add_rule : clique -> rule -> t -> t
  
  val rules_for : constant -> t -> rule list

end = struct (* {{{ *)

  type sequent = { eigen : term; context : term; conclusion : term }
  and alignment = { arg2sequent : int IM.t; keys : (string * int) list }
  and rule = {
    to_match : sequent list;
    to_remove : sequent list;
    alignment : alignment option;
    guard : term option;
    new_goal : sequent option;
    nargs : int [@default 0];
    pattern : Constants.t list;
  }
  [@@ deriving show]
  type t = {
    cliques : Constants.Set.t Constants.Map.t;
    rules : rule list Constants.Map.t
  }
  type clique = Constants.Set.t

  let empty = { cliques = Constants.Map.empty; rules = Constants.Map.empty }

  let new_clique cl ({ cliques } as chr) =
    if cl = [] then error "empty clique";
    let c = List.fold_right Constants.Set.add cl Constants.Set.empty in
    Constants.(Map.iter (fun _ c' ->
      if not (Set.is_empty (Set.inter c c')) && not (Set.equal c c') then
        error ("overlapping constraint cliques: {" ^
          String.concat "," (List.map Constants.show (Set.elements c))^"} {" ^
          String.concat "," (List.map Constants.show (Set.elements c'))^ "}")
    ) cliques);
    let cliques =
      List.fold_right (fun x cliques -> Constants.Map.add x c cliques) cl cliques in
    { chr with cliques }, c

  let clique_of c { cliques } =
    try Some (Constants.Map.find c cliques)
    with Not_found -> None

  let add_rule cl r ({ rules } as chr) =
    let rules = Constants.Set.fold (fun c rules ->
      try      
        let rs = Constants.Map.find c rules in
        Constants.Map.add c (rs @ [r]) rules
      with Not_found -> Constants.Map.add c [r] rules)
      cl rules in
    { chr with rules }


  let rules_for c { rules } =
    try Constants.Map.find c rules
    with Not_found -> []

end (* }}} *)

module CompilerState = State(struct type t = unit end)

module CustomConstraint : sig
    type ('a,'b) source =
      | CompilerState of 'b CompilerState.component * ('b -> 'a)
      | Other of (unit -> 'a)
    
    type 'a component

    (* Must be purely functional *)
    val declare :
      name:string ->
      pp:(Fmt.formatter -> 'a -> unit) ->
      init:('a,'b) source ->
        'a component

    type t
    val init : CompilerState.t -> t 
    val get : 'a component -> t -> 'a
    val set : 'a component -> t -> 'a -> t
    val update : 'a component -> t -> ('a -> 'a) -> t
    val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b
    val pp : Format.formatter -> t -> unit
     
  end = struct 

    type ('a,'b) source =
      | CompilerState of 'b CompilerState.component * ('b -> 'a)
      | Other of (unit -> 'a)

    include State(CompilerState)
      
    let declare ~name ~pp ~init =
      let init s = match init with
        | Other f -> f ()
        | CompilerState (c,f) -> f (CompilerState.get c s) in
      declare ~name ~pp ~init

  end (* }}} *)

module CustomFunctorCompilation : sig
  val declare_singlequote_compilation : string -> (CompilerState.t -> F.t -> CompilerState.t * term) -> unit
  val declare_backtick_compilation : string -> (CompilerState.t -> F.t -> CompilerState.t * term) -> unit
  
  val compile_singlequote : CompilerState.t -> F.t -> CompilerState.t * term
  val compile_backtick : CompilerState.t -> F.t -> CompilerState.t * term

  val is_singlequote : F.t -> bool
  val is_backtick : F.t -> bool

end = struct

  let is_singlequote x =
    let s = F.show x in
    let len = String.length s in
    len > 2 && s.[0] == '\'' && s.[len-1] == '\''

  let is_backtick x =
    let s = F.show x in
    let len = String.length s in
    len > 2 && s.[0] == '`' && s.[len-1] == '`'

  let singlequote = ref None
  let backtick = ref None

  let declare_singlequote_compilation name f =
    match !singlequote with
    | None -> singlequote := Some(name,f)
    | Some(oldname,_) ->
         error("Only one custom compilation of 'ident' is supported. Current: "
           ^ oldname ^ ", new: " ^ name)
  let declare_backtick_compilation name f =
    match !backtick with
    | None -> backtick := Some(name,f)
    | Some(oldname,_) ->
         error("Only one custom compilation of `ident` is supported. Current: "
           ^ oldname ^ ", new: " ^ name)

  let compile_singlequote state x =
    match !singlequote with
    | None -> state, snd (Constants.funct_of_ast x)
    | Some(_,f) -> f state x
  let compile_backtick state x =
    match !backtick with
    | None -> state, snd (Constants.funct_of_ast x)
    | Some(_,f) -> f state x

end

(* true=input, false=output *)
type mode = bool list [@@deriving show]

module TwoMapIndexingTypes = struct (* {{{ *)

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

type idx = {
  src : clause_src list;
  map : (clause list * clause list * clause list Elpi_ptmap.t) Elpi_ptmap.t
}

end (* }}} *)

module UnifBitsTypes = struct (* {{{ *)

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
    src : clause_src list;
    map : (clause * int) list Elpi_ptmap.t  (* timestamp *)
  }

end (* }}} *)

type idx = TwoMapIndexingTypes.idx
type key = TwoMapIndexingTypes.key
type clause = TwoMapIndexingTypes.clause = {
  depth : int;
  args : term list;
  hyps : term list;
  vars : int;
  key : key;
  mode : mode;
}

type mode_decl =
  | Mono of mode
  | Multi of (constant * (constant * constant) list) list

(* An elpi program, as parsed.  But for idx and query_depth that are threaded
   around in the main loop, chr and modes are globally stored in Constraints
   and Clausify. *)
type clause_w_info = {
  clloc : CData.t;
  clargsname : string list;
  clbody : clause;
}

let drop_clause_info { clbody } = clbody

type macro_declaration = (Elpi_ast.term * Ploc.t) F.Map.t
type type_declaration = {
  tname : constant;
  tnargs : int;
  ttype : term;
}

let todopp fmt _ = error "not implemented"

let modes : mode_decl Constants.Map.t CompilerState.component =
  CompilerState.declare ~pp:todopp ~name:"elpi:modes"
    ~init:(fun () -> Constants.Map.empty)
let chr : CHR.t CompilerState.component =
  CompilerState.declare ~pp:todopp ~name:"elpi:chr"
    ~init:(fun () -> CHR.empty)
let declared_types : type_declaration list CompilerState.component =
  CompilerState.declare ~pp:todopp ~name:"elpi:declared_types"
    ~init:(fun () -> [])
let clauses_w_info : clause_w_info list CompilerState.component =
  CompilerState.declare ~pp:todopp ~name:"elpi:clauses_w_info"
    ~init:(fun () -> [])
let macros : macro_declaration CompilerState.component =
  CompilerState.declare ~pp:todopp ~name:"elpi:macros"
    ~init:(fun () -> F.Map.empty)

type program = {
  (* n of sigma/local-introduced variables *)
  query_depth : int;
  (* the lambda-Prolog program: an indexed list of clauses *) 
  compiled_program : prolog_prog [@printer (pp_extensible pp_prolog_prog)];

  compiler_state : CompilerState.t;
}

type query = { 
  qloc : Ploc.t;
  qnames : int StrMap.t;
  qdepth : int;
  qenv : env;
  qterm : term;
  qconstraints : CustomConstraint.t;
}

type prolog_prog += Index of idx
let () = extend_printer pp_prolog_prog (fun fmt -> function
  | Index _ -> Fmt.fprintf fmt "<prolog_prog>";`Printed
  | _ -> `Passed)
let wrap_prolog_prog x = Index x
let unwrap_prolog_prog = function Index x -> x | _ -> assert false

exception No_clause
exception No_more_steps

type custom_constraints = CustomConstraint.t
type syntactic_constraints = stuck_goal list

type solution = {
  arg_names : int StrMap.t;
  assignments : env;
  constraints : syntactic_constraints;
  custom_constraints : custom_constraints;
}
type outcome = Success of solution | Failure | NoMoreSteps

type hyps = clause_src list

let register_custom, register_custom_full, lookup_custom, all_custom =
 let (customs :
      (* Must either raise No_clause or succeed with the list of new goals *)
      ('a, depth:int -> hyps -> solution -> term list -> term list * custom_constraints)
      Hashtbl.t)
   =
     Hashtbl.create 17 in
 let check s = 
    if s = "" then
      anomaly ("Custom predicate name must be non empty");
    let idx = Constants.from_stringc s in
    if Hashtbl.mem customs idx then
      anomaly ("Duplicate custom predicate name " ^ s);
    idx in
 (fun s f ->
    let idx = check s in
    Hashtbl.add customs idx
      (fun ~depth _ { custom_constraints } args ->
         f ~depth args, custom_constraints)),
 (fun s f ->
    let idx = check s in
    Hashtbl.add customs idx f),
 Hashtbl.find customs,
 (fun () -> Hashtbl.fold (fun k _ acc -> k::acc) customs [])
;;

let is_custom_declared x =
  (try let _f = lookup_custom x in true
   with Not_found -> false)
  || x == Constants.declare_constraintc
  || x == Constants.print_constraintsc
  || x == Constants.cutc
;;

let of_term x = x

(* vim: set foldmethod=marker: *)
