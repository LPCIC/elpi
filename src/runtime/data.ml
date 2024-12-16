(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* Internal term representation *)

open Elpi_util
open Elpi_parser

module Fmt = Format
module F = Ast.Func
open Util

(******************************************************************************
  Terms: data type definition and printing
 ******************************************************************************)

(* Heap and Stack
 *
 * We use the same data type (term) the following beasts:
 *   preterm = Pure term <= Heap term <= Stack term
 *
 * - only Stack terms can contain Arg nodes
 * - Heap terms can contain UVar nodes
 * - Pure terms contain no Arg and no UVar nodes
 * - a preterm is a Pure term that may contain "%Arg3" constants.  These
 *   constants morally represent Arg nodes
 *
 * Preterms are only used during compilation.  Beta-reduction, needed for
 * macro expansion for example, is only defined on Heap terms.  We hence
 * separate the compilation of clauses into:
 *   AST -> preterm -> term -> clause
 *
 * Heap and Stack terms are used during execution. The query if the
 * root of Heap terms, clauses are Stack terms and are eventually copied
 * to the Heap.
 * Invariant: a Heap term never points to a Stack term.
 *
 *)

module Term = struct

(* To be instantiated after the dummy term is defined *)
let pp_oref = mk_spaghetti_printer ()

let id_term = UUID.make ()

(* This data type is open since runtime (traced or not) adds to it
   its own representation of constraints, projectable to the type
   suspended_goal below *)
type 'unification_def stuck_goal_kind = ..
let pp_stuck_goal_kind p1 fmt x = ()
let show_stuck_goal_kind p1 _ = ""
let equal_stuck_goal_kind _ x y = x == y
type 'unification_def stuck_goal_kind +=
  | Unification of 'unification_def

type ttype =
  | TConst of constant
  | TApp of constant * ttype * ttype list
  | TPred of bool * ((Mode.t * ttype) list) (* The bool is for functionality *)
  | TArr of ttype * ttype
  | TCData of CData.t
  | TLam of ttype (* this is for parametrized typeabbrevs *)
  [@@ deriving show, ord]

type term =
  (* Pure terms *)
  | Const of constant
  | Lam of term
  | App of constant * term * term list
  (* Optimizations *)
  | Cons of term * term
  | Nil
  | Discard
  (* FFI *)
  | Builtin of constant * term list
  | CData of CData.t
  (* Heap terms: unif variables in the query *)
  | UVar of uvar_body * (*depth:*)int * (*argsno:*)int
  | AppUVar of uvar_body * (*depth:*)int * term list
  (* Clause terms: unif variables used in clauses *)
  | Arg of (*id:*)int * (*argsno:*)int
  | AppArg of (*id*)int * term list
and uvar_body = {
  mutable contents : term [@printer (pp_spaghetti_any ~id:id_term pp_oref)];
  mutable uid_private : int; (* unique name, the sign is flipped when blocks a constraint *)
}
[@@deriving show, ord]

let cons2tcons ?(loc=Loc.initial"") = function Const t -> TConst t | _ -> anomaly ~loc "Unreachable branch"

(* we use this projection to be sure we ignore the sign *)
let uvar_id { uid_private } = abs uid_private [@@inline];;
let uvar_is_a_blocker   { uid_private } = uid_private < 0 [@@inline];;
let uvar_isnt_a_blocker { uid_private } = uid_private > 0 [@@inline];;

let uvar_set_blocker r   = r.uid_private <- -(uvar_id r) [@@inline];;
let uvar_unset_blocker r = r.uid_private <-  (uvar_id r) [@@inline];;

type clause = {
    depth : int;
    args : term list;
    hyps : term list;
    vars : int;
    mode : Mode.hos;        (* CACHE to avoid allocation in get_clauses *)
    loc : Loc.t option; (* debug *)
    mutable timestamp : int list; (* for grafting *)
}
[@@deriving show, ord]

type grafting_time = int list
[@@deriving show, ord]
let compare_constant = Util.compare_constant
type times = (grafting_time * constant) StrMap.t
[@@deriving show, ord]

type stuck_goal = {
  mutable blockers : blockers;
  kind : unification_def stuck_goal_kind;
}
and blockers = uvar_body list
and unification_def = {
  adepth : int;
  env : term array;
  bdepth : int;
  a : term;
  b : term;
  matching: bool;
}
and clause_src = { hdepth : int; hsrc : term }
and prolog_prog = {
  src : clause_src list; (* hypothetical context in original form, for CHR *)
  index : index;
}

(* These two are the same, but the latter should not be mutated *)

and clause_list = clause Bl.t
and index = first_lvl_idx
and first_lvl_idx = {
  idx : second_lvl_idx Ptmap.t;
  time : int; (* ticking clock, to timestamp clauses so to recover total order after retrieval if necessary. positive at compile time, negative at run time *)
  times : times; (* timestamp of named clauses, for grafting at compile time *)
}
and second_lvl_idx =
| TwoLevelIndex of {
    mode : Mode.hos;
    argno : int;
    all_clauses : clause_list;        (* when the query is flexible *)
    flex_arg_clauses : clause_list;   (* when the query is rigid but arg_id ha nothing *)
    arg_idx : clause_list Ptmap.t;    (* when the query is rigid (includes in each binding flex_arg_clauses) *)
  }
| BitHash of {
    mode : Mode.hos;
    args : int list;
    args_idx : clause_list Ptmap.t; (* clause, insertion time *)
  }
| IndexWithDiscriminationTree of {
    mode : Mode.hos;
    arg_depths : int list;   (* the list of args on which the trie is built *)
    args_idx : clause Discrimination_tree.t; 
}
[@@deriving show]

let stop = ref false
let close_index ({idx; time; times} : index) : index =
  { idx =idx; time = 0; times = StrMap.empty }

type constraints = stuck_goal list
type hyps = clause_src list

type suspended_goal = {
  context : hyps;
  goal : int * term
}

(** 
  Used to index the parameters of a predicate P
  - [MapOn N] -> N-th argument at depth 1 (head symbol only)
  - [Hash L]  -> L is the list of depths given by the urer for the parameters of
                 P. Indexing is done by hashing all the parameters with a non
                 zero depth and comparing it with the hashing of the parameters
                 of the query
  - [DiscriminationTree L] ->
            we use the same logic of Hash, except we use DiscriminationTree to discriminate
            clauses
*)
type indexing =
  | MapOn of int
  | Hash of int list
  | DiscriminationTree of int list
[@@deriving show]

let mkLam x = Lam x [@@inline]
let mkApp c x xs = App(c,x,xs) [@@inline]
let mkCons hd tl = Cons(hd,tl) [@@inline]
let mkNil = Nil
let mkDiscard = Discard
let mkBuiltin c args = Builtin(c,args) [@@inline]
let mkCData c = CData c [@@inline]
let mkUVar r d ano = UVar(r,d,ano) [@@inline]
let mkAppUVar r d args = AppUVar(r,d,args) [@@inline]
let mkArg i ano = Arg(i,ano) [@@inline]
let mkAppArg i args = AppArg(i,args) [@@inline]

module C = struct

  let { CData.cin = in_int; isc = is_int; cout = out_int } as int =
    Ast.cint
  let is_int = is_int
  let to_int = out_int
  let of_int x = CData (in_int x)

  let { CData.cin = in_float; isc = is_float; cout = out_float } as float =
    Ast.cfloat
  let is_float = is_float
  let to_float = out_float
  let of_float x = CData (in_float x)
  
  let { CData.cin = in_string; isc = is_string; cout = out_string } as string =
    Ast.cstring
  let is_string = is_string
  let to_string x = out_string x
  let of_string x = CData (in_string x)

  let loc = Ast.cloc
  let is_loc = loc.CData.isc
  let to_loc = loc.CData.cout
  let of_loc x = CData (loc.CData.cin x)

end

let destConst = function Const x -> x | _ -> assert false

(* Our ref data type: creation and dereference.  Assignment is defined
   After the constraint store, since assigning may wake up some constraints *)
let oref =
  let uid = ref 0 in
  fun x -> incr uid; assert(!uid > 0); { contents = x; uid_private = !uid }
let (!!) { contents = x } = x

(* Arg/AppArg point to environments, here the empty one *)
type env = term array
let empty_env = [||]
end
include Term


(* Object oriented State.t: borns at compilation time and survives as run time *)
module State : sig

  type descriptor
  val new_descriptor : unit -> descriptor
  val merge_descriptors : descriptor -> descriptor -> descriptor

  (* filled in with components *)
  type 'a component
  val declare :
    descriptor:descriptor ->
    name:string -> pp:(Format.formatter -> 'a -> unit) ->
    init:(unit -> 'a) ->
    clause_compilation_is_over:('a -> 'a) ->
    ?goal_compilation_begins:('a -> 'a) ->
    compilation_is_over:('a -> 'a option) ->
    execution_is_over:('a -> 'a option) ->
    unit ->
     'a component

  (* an instance of the State.t type *)
  type t

  (* Lifetime:
     - init (called once)
     - end_clause_compilation (called after every clause)
     - end_compilation (just once before running)
     - end_execution (just once after running)
  *)
  
  val init : descriptor -> t
  val end_clause_compilation : t -> t
  val begin_goal_compilation : t -> t
  val end_compilation : t -> t
  val end_execution : t -> t

  val get : 'a component -> t -> 'a
  val set : 'a component -> t -> 'a -> t
  val drop : 'a component -> t -> t
  val update : 'a component -> t -> ('a -> 'a) -> t
  val update_return : 'a component -> t -> ('a -> 'a * 'b) -> t * 'b
  val pp : Format.formatter -> t -> unit

  val dummy : t

end = struct

  type stage =
    | Dummy
    | Compile_prog
    | Compile_goal
    | Run
    | Halt

  type 'a component = string
  type extension = {
    init : unit -> Obj.t;
    end_clause : Obj.t -> Obj.t;
    begin_goal : Obj.t -> Obj.t;
    end_comp : Obj.t -> Obj.t option;
    end_exec : Obj.t -> Obj.t option;
    pp   : Format.formatter -> Obj.t -> unit;
  }
  type descriptor = extension StrMap.t ref

  type t = { data : Obj.t StrMap.t; stage : stage; extensions : descriptor }
  let dummy : t = { data = StrMap.empty; stage = Dummy; extensions = ref StrMap.empty }
  let descriptor { extensions = x } = x
 
  let new_descriptor () : descriptor = ref StrMap.empty
  let merge_descriptors m1 m2 =
    ref (StrMap.merge (fun n e1 e2 ->
      match e1, e2 with
      | None, None -> None
      | Some x, None -> Some x
      | None, Some x -> Some x
      | Some _, Some _ -> error ("The state cannot contain two components named "^n) )
      !m1 !m2)

  let get name { data = t } =
    try Obj.obj (StrMap.find name t)
    with Not_found ->
       anomaly ("State.get: component " ^ name ^ " not found")

  let set name ({ data } as x) v = { x with data = StrMap.add name (Obj.repr v) data }
  let drop name ({ data } as x) = { x with data = StrMap.remove name data }
  let update name ({ data } as x) f =
    { x with data = StrMap.add name (Obj.repr (f (Obj.obj (StrMap.find name data)))) data }
  let update_return name t f =
    let x = get name t in
    let x, res = f x in
    let t = set name t x in
    t, res

  let declare ~descriptor:extensions ~name ~pp ~init ~clause_compilation_is_over ?(goal_compilation_begins = fun x -> x) ~compilation_is_over ~execution_is_over () =
    if StrMap.mem name !extensions then
      anomaly ("Extension "^name^" already declared");
    extensions := StrMap.add name {
        init = (fun x -> Obj.repr (init x));
        pp = (fun fmt x -> pp fmt (Obj.obj x));
        end_clause = (fun x -> Obj.repr (clause_compilation_is_over (Obj.obj x)));
        begin_goal = (fun x -> Obj.repr (goal_compilation_begins (Obj.obj x)));
        end_comp = (fun x -> option_map Obj.repr (compilation_is_over (Obj.obj x)));
        end_exec = (fun x -> option_map Obj.repr (execution_is_over (Obj.obj x)));
      }
      !extensions;
    name

  let init extensions : t =
    let data = StrMap.fold (fun name { init } acc ->
      let o = init () in
      StrMap.add name o acc)
      !extensions StrMap.empty in
    {
      data;
      stage = Compile_prog;
      extensions;
    }

  let end_clause_compilation { data = m; stage = s; extensions } : t =
    assert(s = Compile_prog);
    { data = StrMap.fold (fun name obj acc ->
        let o = (StrMap.find name !extensions).end_clause obj in
        StrMap.add name o acc) m StrMap.empty;
      stage = s;
      extensions }

  let begin_goal_compilation { data = m; stage = s; extensions } : t =
    assert(s = Compile_prog);
    { data = StrMap.fold (fun name obj acc ->
      let o = (StrMap.find name !extensions).begin_goal obj in
      StrMap.add name o acc) m StrMap.empty;
    stage = Compile_goal;
    extensions }

  let end_compilation { data = m; stage = s; extensions } : t =
    assert(s = Compile_goal);
    { data = StrMap.fold (fun name obj acc ->
        match (StrMap.find name !extensions).end_comp obj with
        | None -> acc
        | Some o -> StrMap.add name o acc) m StrMap.empty;
      stage = Run;
      extensions }

  let end_execution { data = m; stage = s; extensions } : t =
    assert(s = Run);
    { data = StrMap.fold (fun name obj acc ->
        match (StrMap.find name !extensions).end_exec obj with
        | None -> acc
        | Some o -> StrMap.add name o acc) m StrMap.empty;
      stage = Halt;
      extensions }

  let pp fmt { data = t; stage = s; extensions } : unit =
    StrMap.iter (fun name { pp } ->
      try pp fmt (StrMap.find name t)
      with Not_found -> ())
    !extensions

end

let elpi_state_descriptor = State.new_descriptor ()

(* This module contains the symbols reserved by Elpi and the ones
   declared by the API client via declare_global_symbol statically
   (eg the API must be called in a OCaml toplevel value).

   These symbols are part of any Elpi program.
   The runtime only uses the symbols listed in the module signature,
   the declared ones are read by the compiler and propagated to the runtime.
*)
module Global_symbols : sig

  (* Table used at link time *)
  type t = {
    (* Ast (functor name) -> negative int n (constant) * hashconsed (Const n) *)
    mutable s2ct : (constant * term) Ast.Func.Map.t;
    mutable c2s : string Constants.Map.t;
    (* negative *)
    mutable last_global : int;

    (* Once the system is initialized this shall change no more *)
    mutable locked: bool;
    mutable c2mode : Mode.hos Constants.Map.t;
  }
  val table : t

  (* Static initialization, eg link time *)
  val declare_global_symbol : string -> constant
  val lock : unit -> unit

  val cutc     : constant
  val andc     : constant
  val orc      : constant
  val implc    : constant
  val rimplc   : constant
  val pic      : constant
  val sigmac   : constant
  val eqc      : constant
  val rulec    : constant
  val consc    : constant
  val nilc     : constant
  val entailsc : constant
  val nablac   : constant
  val asc      : constant
  val arrowc   : constant
  val uvarc    : constant
  val propc    : constant

  val ctypec   : constant
  val variadic : constant

  val spillc   : constant
  val truec    : constant

  val declare_constraintc : constant
  val print_constraintsc  : constant
  val findall_solutionsc  : constant

end = struct

type t = {
  mutable s2ct : (constant * term) Ast.Func.Map.t;
  mutable c2s : string Constants.Map.t;
  mutable last_global : int;
  mutable locked : bool;
  mutable c2mode : Mode.hos Constants.Map.t;
}
[@@deriving show]

let table = {
  last_global = 0;
  s2ct = Ast.Func.Map.empty;
  c2s = Constants.Map.empty;
  locked = false;
  c2mode = Constants.Map.empty
}

let declare_global_symbol str =
  let x = Ast.Func.from_string str in
  try fst @@ Ast.Func.Map.find x table.s2ct
  with Not_found ->
    if table.locked then
      Util.anomaly "declare_global_symbol called after initialization";
    table.last_global <- table.last_global - 1;
    let n = table.last_global in
    let t = Const n in
    table.s2ct <- Ast.Func.Map.add x (n,t) table.s2ct;
    table.c2s <- Constants.Map.add n str table.c2s;
    table.c2mode <- Constants.Map.add n [] table.c2mode;
    n

let declare_global_symbol_for_builtin str =
  let x = Ast.Func.from_string str in
  if table.locked then
    Util.anomaly "declare_global_symbol_for_builtin called after initialization";
  try fst @@ Ast.Func.Map.find x table.s2ct
  with Not_found ->
    table.last_global <- table.last_global - 1;
    let n = table.last_global in
    let t = Builtin(n,[]) in
    table.s2ct <- Ast.Func.Map.add x (n,t) table.s2ct;
    table.c2s <- Constants.Map.add n str table.c2s;
    table.c2mode <- Constants.Map.add n [] table.c2mode;
    n

let lock () = table.locked <- true

let andc                = declare_global_symbol F.(show andf)
let arrowc              = declare_global_symbol F.(show arrowf)
let asc                 = declare_global_symbol "as"
let consc               = declare_global_symbol F.(show consf)
let entailsc            = declare_global_symbol "?-"
let eqc                 = declare_global_symbol F.(show eqf)
let uvarc               = declare_global_symbol "uvar"
let implc               = declare_global_symbol F.(show implf)
let nablac              = declare_global_symbol "nabla"
let nilc                = declare_global_symbol F.(show nilf)
let orc                 = declare_global_symbol F.(show orf)
let pic                 = declare_global_symbol F.(show pif)
let rimplc              = declare_global_symbol F.(show rimplf)
let rulec               = declare_global_symbol "rule"
let sigmac              = declare_global_symbol F.(show sigmaf)
let spillc              = declare_global_symbol F.(show spillf)
let truec               = declare_global_symbol F.(show truef)
let ctypec              = declare_global_symbol F.(show ctypef)
let propc               = declare_global_symbol "prop"
let variadic            = declare_global_symbol "variadic"

let declare_constraintc = declare_global_symbol "declare_constraint"
let cutc                = declare_global_symbol_for_builtin F.(show cutf)
let print_constraintsc  = declare_global_symbol_for_builtin "print_constraints"
let findall_solutionsc  = declare_global_symbol_for_builtin "findall_solutions"

end

(* This term is hashconsed here *)
let dummy = App (Global_symbols.cutc,Const Global_symbols.cutc,[])
let dummy_uvar_body = { contents = dummy; uid_private = 0 }

module CHR : sig

  (* a set of rules *)
  type t

  (* a set of predicates contributing to represent a constraint *)
  type clique

  type sequent = { eigen : term; context : term; conclusion : term }
  and rule = {
    to_match : sequent list;
    to_remove : sequent list;
    patsno : int;
    guard : term option;
    new_goal : sequent option;
    nargs : int [@default 0];
    pattern : constant list;
    rule_name : string;
    rule_loc : Loc.t;
  }
  val pp_sequent : Fmt.formatter -> sequent -> unit
  val show_sequent : sequent -> string
  val pp_rule : Fmt.formatter -> rule -> unit
  val show_rule : rule -> string

  val empty : t

  val new_clique : (constant -> Ast.Func.t) -> constant list -> constant list -> t -> t * clique
  val clique_of : constant -> t -> (Constants.Set.t * Constants.Set.t) option
  val add_rule : clique -> rule -> t -> t
  val in_clique : clique -> constant -> bool
  
  val rules_for : constant -> t -> rule list

  val pp : Fmt.formatter -> t -> unit
  val pp_clique : Fmt.formatter -> clique -> unit
  val show : t -> string

end = struct (* {{{ *)

  type clique = {ctx_filter: Constants.Set.t; clique: Constants.Set.t} [@@deriving show]
  type sequent = { eigen : term; context : term; conclusion : term }
  and rule = {
    to_match : sequent list;
    to_remove : sequent list;
    patsno : int;
    guard : term option;
    new_goal : sequent option;
    nargs : int [@default 0];
    pattern : constant list;
    rule_name : string;
    rule_loc : Loc.t;
  }
  [@@ deriving show]
  type t = {
    cliques : clique Constants.Map.t;
    rules : rule list Constants.Map.t
  }
  [@@ deriving show]

  let empty = { cliques = Constants.Map.empty; rules = Constants.Map.empty }

  let in_clique {clique; ctx_filter} c = Constants.Set.mem c clique

  let new_clique show_constant hyps cl ({ cliques } as chr) =
    let open Constants in
    if cl = [] then error "empty clique";
    let c = Set.of_list cl in
    let ctx_filter = Set.of_list hyps in
    
    (* Check new inserted clique is valid *)
    let build_clique_str c =
      Printf.sprintf "{ %s }" @@ String.concat "," (List.map (fun x -> Ast.Func.show @@ show_constant x) (Set.elements c)) 
    in
    let old_ctx_filter = ref None in
    let exception Stop in
    (try 
      Map.iter (fun _ ({clique=c';ctx_filter=ctx_filter'}) ->
        if Set.equal c c' then (old_ctx_filter := Some ctx_filter'; raise Stop)
        else if not (Set.disjoint c c') then (* different, not disjoint clique *)
          error ("overlapping constraint cliques:" ^ build_clique_str c ^ "and" ^ build_clique_str c')
      ) cliques;
    with Stop -> ());
    let clique = 
      {ctx_filter = Set.union ctx_filter (Option.value ~default:Set.empty !old_ctx_filter); clique=c} in
    let (cliques: clique Constants.Map.t) =
      List.fold_left (fun cliques x -> Constants.Map.add x clique cliques) cliques cl in
    { chr with cliques }, clique

  let clique_of c { cliques } =
    try Some (let res = Constants.Map.find c cliques in res.clique, res.ctx_filter)
    with Not_found -> None

  let add_rule ({clique}: clique) r ({ rules } as chr) =
    let rules = Constants.Set.fold (fun c rules ->
      try
        let rs = Constants.Map.find c rules in
        Constants.Map.add c (rs @ [r]) rules
      with Not_found -> Constants.Map.add c [r] rules)
      clique rules in
    { chr with rules }


  let rules_for c { rules } =
    try Constants.Map.find c rules
    with Not_found -> []

end (* }}} *)

(* An elpi program, as parsed.  But for idx and query_depth that are threaded
   around in the main loop, chr and modes are globally stored in Constraints
   and Clausify. *)
type clause_w_info = {
  clloc : CData.t;
  clargsname : string list;
  clbody : clause;
}
[@@ deriving show]

exception No_clause
exception No_more_steps


module Conversion = struct

  type extra_goal = .. 

  type extra_goal +=
    | Unify of term * term
    | RawGoal of term
  type extra_goals = extra_goal list
  type extra_goals_postprocessing = extra_goals -> State.t -> State.t * extra_goals
  
  let extra_goals_postprocessing : extra_goals_postprocessing State.component = State.declare
    ~descriptor:elpi_state_descriptor
    ~name:"elpi:extra_goals_postprocessing"
    ~pp:(fun _ _ -> ())
    ~clause_compilation_is_over:(fun b -> b)
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun x -> Some x)
    ~init:(fun () -> (); fun x s -> s, x)
    ()

  type ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list
  [@@deriving show]

  type 'a embedding =
    depth:int ->
    State.t -> 'a -> State.t * term * extra_goals

  type 'a readback =
    depth:int ->
    State.t -> term -> State.t * 'a * extra_goals

  type 'a t = {
    ty : ty_ast;
    pp_doc : Format.formatter -> unit -> unit [@opaque];
    pp : Format.formatter -> 'a -> unit [@opaque];
    embed : 'a embedding [@opaque];   (* 'a -> term *)
    readback : 'a readback [@opaque]; (* term -> 'a *)
  }
  [@@deriving show]

  exception TypeErr of ty_ast * int * term (* a type error at data conversion time *)

type prec_level =
  | Arrow
  | AppArg

let need_par x y =
  match x,y with
  | Some AppArg, Arrow -> true
  | Some AppArg, AppArg -> true
  | Some Arrow, Arrow -> true
  | Some Arrow, AppArg -> false
  | None, _ -> false

let with_par p1 p2 s = if need_par p1 p2 then "("^s^")" else s

let rec show_ty_ast ?prec = function
  | TyName s -> s
  | TyApp ("->",src,[tgt]) ->
      let src = show_ty_ast ~prec:Arrow src in
      let tgt = show_ty_ast tgt in
      with_par prec Arrow (src ^" -> "^ tgt)
  | TyApp (s,x,xs) ->
      let t = String.concat " " (s :: List.map (show_ty_ast ~prec:AppArg) (x::xs)) in
      with_par prec AppArg t

let term_of_extra_goal = function
  | Unify(a,b) -> Builtin(Global_symbols.eqc,[a;b])
  | RawGoal x -> x
  | x ->
      Util.anomaly (Printf.sprintf "Unprocessed extra_goal: %s.\nOnly %s and %s can be left unprocessed,\nplease call API.RawData.set_extra_goals_postprocessing.\n"
        (Obj.Extension_constructor.(name (of_val x)))
        (Obj.Extension_constructor.(name (of_val (Unify(dummy,dummy)))))
        (Obj.Extension_constructor.(name (of_val (RawGoal dummy)))))
        
end

module ContextualConversion = struct

  type ty_ast = Conversion.ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list
  [@@deriving show]

  type ('a,'hyps,'constraints) embedding =
    depth:int -> 'hyps -> 'constraints ->
    State.t -> 'a -> State.t * term * Conversion.extra_goals

  type ('a,'hyps,'constraints) readback =
    depth:int -> 'hyps -> 'constraints ->
    State.t -> term -> State.t * 'a * Conversion.extra_goals

  type ('a,'hyps,'constraints) t = {
    ty : ty_ast;
    pp_doc : Format.formatter -> unit -> unit [@opaque];
    pp : Format.formatter -> 'a -> unit [@opaque];
    embed : ('a,'hyps,'constraints) embedding [@opaque];   (* 'a -> term *)
    readback : ('a,'hyps,'constraints) readback [@opaque]; (* term -> 'a *)
  }
  [@@deriving show]

  type ('hyps,'constraints) ctx_readback =
    depth:int -> hyps -> constraints -> State.t -> State.t * 'hyps * 'constraints * Conversion.extra_goals

  let unit_ctx : (unit,unit) ctx_readback = fun ~depth:_ _ _ s -> s, (), (), []
  let raw_ctx : (hyps,constraints) ctx_readback = fun ~depth:_ h c s -> s, h, c, []


  let (!<) { ty; pp_doc; pp; embed; readback; } = {
    Conversion.ty; pp; pp_doc;
    embed = (fun ~depth s t -> embed ~depth () () s t);
    readback = (fun ~depth s t -> readback ~depth () () s t);
  }

  let (!>) { Conversion.ty; pp_doc; pp; embed; readback; } = {
    ty; pp; pp_doc;
    embed = (fun ~depth _ _ s t -> embed ~depth s t);
    readback = (fun ~depth _ _ s t -> readback ~depth s t);
  }

  let (!>>) (f : 'a Conversion.t -> 'b Conversion.t) cc =
  let mk h c { ty; pp_doc; pp; embed; readback; } = {
    Conversion.ty; pp; pp_doc;
    embed = (fun ~depth s t -> embed ~depth h c s t);
    readback = (fun ~depth s t -> readback ~depth h c s t);
  } in
  let mk_pp { ty; pp_doc; pp; } = {
    Conversion.ty; pp; pp_doc;
    embed = (fun ~depth s t -> assert false);
    readback = (fun ~depth s t -> assert false);
  } in
  let { Conversion.ty; pp; pp_doc } = f (mk_pp cc) in
  {
    ty;
    pp;
    pp_doc;
    embed = (fun ~depth h c s t -> (f (mk h c cc)).embed ~depth s t);
    readback = (fun ~depth h c s t -> (f (mk h c cc)).readback ~depth s t);
  }
  
  let (!>>>) (f : 'a Conversion.t -> 'b Conversion.t -> 'c Conversion.t) cc dd = 
  let mk h c { ty; pp_doc; pp; embed; readback; } = {
    Conversion.ty; pp; pp_doc;
    embed = (fun ~depth s t -> embed ~depth h c s t);
    readback = (fun ~depth s t -> readback ~depth h c s t);
  } in
  let mk_pp { ty; pp_doc; pp; } = {
    Conversion.ty; pp; pp_doc;
    embed = (fun ~depth s t -> assert false);
    readback = (fun ~depth s t -> assert false);
  } in
  let { Conversion.ty; pp; pp_doc } = f (mk_pp cc)  (mk_pp dd) in
  {
    ty;
    pp;
    pp_doc;
    embed = (fun ~depth h c s t -> (f (mk h c cc) (mk h c dd)).embed ~depth s t);
    readback = (fun ~depth h c s t -> (f (mk h c cc) (mk h c dd)).readback ~depth s t);
  }

  end

let while_compiling : bool State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:compiling"
  ~pp:(fun fmt _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~compilation_is_over:(fun _ -> Some false)
  ~execution_is_over:(fun _ -> Some false) (* we keep it, since API.FlexibleData.Elpi.make needs it *)
  ~init:(fun () -> false)
  ()

module HoasHooks = struct

type descriptor = {
  extra_goals_postprocessing: Conversion.extra_goals_postprocessing option;
}

let new_descriptor () = ref {
  extra_goals_postprocessing = None;
}

let set_extra_goals_postprocessing ~descriptor f =
  match !descriptor with
  | { extra_goals_postprocessing = None } ->
     descriptor := { extra_goals_postprocessing = Some f }
  | { extra_goals_postprocessing = Some _ } ->
      error "set_extra_goals_postprocessing called twice"

end

module CalcHooks = struct

type run = term list -> term
type eval = { code : run; ty_decl : string; }
type descriptor = (constant * eval) list
let new_descriptor () : descriptor ref = ref []

let eval : run Constants.Map.t State.component =
  State.declare ~descriptor:elpi_state_descriptor ~name:"elpi:eval"
  ~clause_compilation_is_over:(fun x -> x)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun _ -> None)
  ~init:(fun () -> Constants.Map.empty)
  ~pp:(fun fmt t -> Constants.Map.pp (fun _ _ -> ()) fmt t)
  ()
end

module BuiltInPredicate = struct

type name = string
type doc = string

type 'a oarg = Keep | Discard
type 'a ioarg = Data of 'a | NoData

type ('function_type, 'inernal_outtype_in, 'internal_hyps, 'internal_constraints) ffi =
  | In    : 't Conversion.t * doc * ('i, 'o,'h,'c) ffi -> ('t -> 'i,'o,'h,'c) ffi
  | Out   : 't Conversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t oarg -> 'i,'o,'h,'c) ffi
  | InOut : 't ioarg Conversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t ioarg -> 'i,'o,'h,'c) ffi

  | CIn    : ('t,'h,'c) ContextualConversion.t * doc * ('i, 'o,'h,'c) ffi -> ('t -> 'i,'o,'h,'c) ffi
  | COut   : ('t,'h,'c) ContextualConversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t oarg -> 'i,'o,'h,'c) ffi
  | CInOut : ('t ioarg,'h,'c) ContextualConversion.t * doc * ('i, 'o * 't option,'h,'c) ffi -> ('t ioarg -> 'i,'o,'h,'c) ffi

  | Easy : doc -> (depth:int -> 'o, 'o,unit,unit) ffi
  | Read : ('h,'c) ContextualConversion.ctx_readback * doc -> (depth:int -> 'h -> 'c -> State.t -> 'o, 'o,'h,'c) ffi
  | Full : ('h,'c) ContextualConversion.ctx_readback * doc -> (depth:int -> 'h -> 'c -> State.t -> State.t * 'o * Conversion.extra_goals, 'o,'h,'c) ffi
  | FullHO : ('h,'c) ContextualConversion.ctx_readback * doc -> (once:(depth:int -> term -> State.t -> State.t) -> depth:int -> 'h -> 'c -> State.t -> State.t * 'o * Conversion.extra_goals, 'o,'h,'c) ffi
  | VariadicIn    : ('h,'c) ContextualConversion.ctx_readback * ('t,'h,'c) ContextualConversion.t * doc -> ('t list -> depth:int -> 'h -> 'c -> State.t -> State.t * 'o, 'o,'h,'c) ffi
  | VariadicOut   : ('h,'c) ContextualConversion.ctx_readback * ('t,'h,'c) ContextualConversion.t * doc -> ('t oarg list -> depth:int -> 'h -> 'c -> State.t -> State.t * ('o * 't option list option), 'o,'h,'c) ffi
  | VariadicInOut : ('h,'c) ContextualConversion.ctx_readback * ('t ioarg,'h,'c) ContextualConversion.t * doc -> ('t ioarg list -> depth:int -> 'h -> 'c -> State.t -> State.t * ('o * 't option list option), 'o,'h,'c) ffi

type t = Pred : name * ('a,unit,'h,'c) ffi * 'a -> t
let pp fmt (Pred(name,_,_)) = Format.fprintf fmt "%s" name
let compare (Pred(name1,_,_)) (Pred(name2,_,_)) = String.compare name1 name2

type doc_spec = DocAbove | DocNext

let pp_comment fmt doc =
  Fmt.fprintf fmt "@?";
  let orig_out = Fmt.pp_get_formatter_out_functions fmt () in
  Fmt.pp_set_formatter_out_functions fmt
    { orig_out with
      Fmt.out_newline = fun () -> orig_out.Fmt.out_string "\n% " 0 3 };
  Fmt.fprintf fmt "@[<hov>";
  Fmt.pp_print_text fmt doc;
  Fmt.fprintf fmt "@]@?";
  Fmt.pp_set_formatter_out_functions fmt orig_out
;;
let pp_ty sep fmt (_,s,_) = Fmt.fprintf fmt " %s%s" s sep
let pp_ty_args = pplist (pp_ty "") " ->" ~pplastelem:(pp_ty "")

module ADT = struct

type ('match_stateful_t,'match_t, 't) match_t =
  | M of (
        (* continuation to call passing subterms *)
        ok:'match_t ->
        (* continuation to call to signal pattern matching failure *)
        ko:(unit -> term) ->
        (* match 't and pass its subterms to ~ok or just call ~ko *)
        't -> term)
  | MS of (
        (* continuation to call passing subterms *)
        ok:'match_stateful_t ->
        (* continuation to call to signal pattern matching failure *)
        ko:(State.t -> State.t * term * Conversion.extra_goals) ->
        (* match 't and pass its subterms to ~ok or just call ~ko *)
        't -> State.t -> State.t * term * Conversion.extra_goals)
type ('build_stateful_t,'build_t) build_t =
  | B of 'build_t
  | BS of 'build_stateful_t

type ('stateful_builder,'builder, 'stateful_matcher, 'matcher,  'self, 'hyps,'constraints) constructor_arguments =
  (* No arguments *)
  | N : (State.t -> State.t * 'self, 'self, State.t -> State.t * term * Conversion.extra_goals, term, 'self, 'hyps,'constraints) constructor_arguments
  (* An argument of type 'a *)
  | A : 'a Conversion.t * ('bs,'b, 'ms,'m, 'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments
  (* An argument of type 'a in context 'hyps,'constraints *)
  | CA : ('a,'hyps,'constraints) ContextualConversion.t * ('bs,'b, 'ms,'m, 'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments
  (* An argument of type 'self *)
  | S : ('bs,'b, 'ms, 'm, 'self, 'hyps,'constraints) constructor_arguments -> ('self -> 'bs, 'self -> 'b, 'self -> 'ms, 'self -> 'm, 'self, 'hyps,'constraints) constructor_arguments
  (* An argument of type `T 'self` for a constainer `T`, like a `list 'self`.
     `S args` above is a shortcut for `C(fun x -> x, args)` *)
  | C : (('self,'hyps,'constraints) ContextualConversion.t -> ('a,'hyps,'constraints) ContextualConversion.t) * ('bs,'b,'ms,'m,'self, 'hyps,'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms,'a -> 'm, 'self, 'hyps,'constraints) constructor_arguments

type ('t,'h,'c) constructor =
  K : name * doc *
      ('build_stateful_t,'build_t,'match_stateful_t,'match_t,'t,'h,'c) constructor_arguments *   (* args ty *)
      ('build_stateful_t,'build_t) build_t *
      ('match_stateful_t,'match_t,'t) match_t
    -> ('t,'h,'c) constructor

type ('t,'h,'c) declaration = {
  ty : Conversion.ty_ast;
  doc : doc;
  pp : Format.formatter -> 't -> unit;
  constructors : ('t,'h,'c) constructor list;
}

type ('b,'m,'t,'h,'c) compiled_constructor_arguments =
  | XN : (State.t -> State.t * 't,State.t -> State.t * term * Conversion.extra_goals, 't,'h,'c) compiled_constructor_arguments
  | XA : ('a,'h,'c) ContextualConversion.t * ('b,'m,'t,'h,'c) compiled_constructor_arguments -> ('a -> 'b, 'a -> 'm, 't,'h,'c) compiled_constructor_arguments

type ('match_t, 't) compiled_match_t =
  (* continuation to call passing subterms *)
  ok:'match_t ->
  (* continuation to call to signal pattern matching failure *)
  ko:(State.t -> State.t * term * Conversion.extra_goals) ->
  (* match 't and pass its subterms to ~ok or just call ~ko *)
  't -> State.t -> State.t * term * Conversion.extra_goals

type ('t,'h,'c) compiled_constructor =
    XK : ('build_t,'matched_t,'t,'h,'c) compiled_constructor_arguments *
    'build_t * ('matched_t,'t) compiled_match_t
  -> ('t,'h,'c) compiled_constructor

type ('t,'h,'c) compiled_adt = (('t,'h,'c) compiled_constructor) Constants.Map.t

let buildk ~mkConst kname = function
| [] -> mkConst kname
| x :: xs -> mkApp kname x xs

let rec readback_args : type a m t h c.
  look:(depth:int -> term -> term) ->
  Conversion.ty_ast -> depth:int -> h -> c -> State.t -> Conversion.extra_goals list -> term ->
  (a,m,t,h,c) compiled_constructor_arguments -> a -> term list ->
    State.t * t * Conversion.extra_goals
= fun ~look ty ~depth hyps constraints state extra origin args convert l ->
    match args, l with
    | XN, [] ->
        let state, x = convert state in
        state, x, List.(concat (rev extra))
    | XN, _ -> raise (Conversion.TypeErr(ty,depth,origin))
    | XA _, [] -> assert false
    | XA(d,rest), x::xs ->
      let state, x, gls = d.readback ~depth hyps constraints state x in
      readback_args ~look ty ~depth hyps constraints state (gls :: extra) origin
        rest (convert x) xs

and readback : type t h c.
  mkinterval:(int -> int -> int -> term list) ->
  look:(depth:int -> term -> term) ->
  alloc:(?name:string -> State.t -> State.t * 'uk) ->
  mkUnifVar:('uk -> args:term list -> State.t -> term) ->
  Conversion.ty_ast -> (t,h,c) compiled_adt -> depth:int -> h -> c -> State.t -> term ->
    State.t * t * Conversion.extra_goals
= fun ~mkinterval ~look ~alloc ~mkUnifVar ty adt ~depth hyps constraints state t ->
  try match look ~depth t with
  | Const c ->
      let XK(args,read,_) = Constants.Map.find c adt in
      readback_args ~look ty ~depth hyps constraints state [] t args read []
  | App(c,x,xs) ->
      let XK(args,read,_) = Constants.Map.find c adt in
      readback_args ~look ty ~depth hyps constraints state [] t args read (x::xs)
  | (UVar _ | AppUVar _) ->
      let XK(args,read,_) = Constants.Map.find Global_symbols.uvarc adt in
      readback_args ~look ty ~depth hyps constraints state [] t args read [t]
  | Discard ->
      let XK(args,read,_) = Constants.Map.find Global_symbols.uvarc adt in
      let state, k = alloc state in
      readback_args ~look ty ~depth hyps constraints state [] t args read
        [mkUnifVar k ~args:(mkinterval 0 depth 0) state]
  | _ -> raise (Conversion.TypeErr(ty,depth,t))
  with Not_found -> raise (Conversion.TypeErr(ty,depth,t))

and adt_embed_args : type m a t h c.
  mkConst:(int -> term) ->
  Conversion.ty_ast -> (t,h,c) compiled_adt -> constant ->
  depth:int -> h -> c ->
  (a,m,t,h,c) compiled_constructor_arguments ->
  (State.t -> State.t * term * Conversion.extra_goals) list ->
    m
= fun ~mkConst ty adt kname ~depth hyps constraints args acc ->
    match args with
    | XN -> fun state ->
        let state, ts, gls =
          List.fold_left (fun (state,acc,gls) f ->
            let state, t, goals = f state in
            state, t :: acc, goals :: gls)
            (state,[],[]) acc in
        state, buildk ~mkConst kname ts, List.(flatten gls)
    | XA(d,args) ->
        fun x ->
          adt_embed_args ~mkConst ty adt kname ~depth hyps constraints
            args ((fun state -> d.embed ~depth hyps constraints state x) :: acc)

and embed : type a h c.
  mkConst:(int -> term) ->
  Conversion.ty_ast -> (Format.formatter -> a -> unit) ->
  (a,h,c) compiled_adt ->
  depth:int -> h -> c -> State.t ->
    a -> State.t * term * Conversion.extra_goals
= fun ~mkConst ty pp adt ->
  let bindings = Constants.Map.bindings adt in
  fun ~depth hyps constraints state t ->
    let rec aux l state =
      match l with
      | [] -> type_error
                  ("Pattern matching failure embedding: " ^ Conversion.show_ty_ast ty ^ Format.asprintf ": %a" pp t)
      | (kname, XK(args,_,matcher)) :: rest ->
        let ok = adt_embed_args ~mkConst ty adt kname ~depth hyps constraints args [] in
        matcher ~ok ~ko:(aux rest) t state in
     aux bindings state

let rec compile_arguments : type b bs m ms t h c.
  (bs,b,ms,m,t,h,c) constructor_arguments -> (t,h,c) ContextualConversion.t -> (bs,ms,t,h,c) compiled_constructor_arguments =
fun arg self ->
  match arg with
  | N -> XN
  | A(d,rest) -> XA(ContextualConversion.(!>) d,compile_arguments rest self)
  | CA(d,rest) -> XA(d,compile_arguments rest self)
  | S rest -> XA(self,compile_arguments rest self)
  | C(fs, rest) -> XA(fs self, compile_arguments rest self)

let rec compile_builder_aux : type bs b m ms t h c. (bs,b,ms,m,t,h,c) constructor_arguments -> b -> bs
  = fun args f ->
    match args with
    | N -> fun state -> state, f
    | A(_,rest) -> fun a -> compile_builder_aux rest (f a)
    | CA(_,rest) -> fun a -> compile_builder_aux rest (f a)
    | S rest -> fun a -> compile_builder_aux rest (f a)
    | C(_,rest) -> fun a -> compile_builder_aux rest (f a)

let compile_builder : type bs b m ms t h c. (bs,b,ms,m,t,h,c) constructor_arguments -> (bs,b) build_t -> bs
  = fun a -> function
    | B f -> compile_builder_aux a f
    | BS f -> f

let rec compile_matcher_ok : type bs b m ms t h c.
  (bs,b,ms,m,t,h,c) constructor_arguments -> ms -> Conversion.extra_goals ref -> State.t ref -> m
  = fun args f gls state ->
    match args with
    | N -> let state', t, gls' = f !state in
           state := state';
           gls := gls';
           t
    | A(_,rest) -> fun a -> compile_matcher_ok rest (f a) gls state
    | CA(_,rest) -> fun a -> compile_matcher_ok rest (f a) gls state
    | S rest -> fun a -> compile_matcher_ok rest (f a) gls state
    | C(_,rest) -> fun a -> compile_matcher_ok rest (f a) gls state

let compile_matcher_ko f gls state () =
  let state', t, gls' = f !state in
  state := state';
  gls := gls';
  t

let compile_matcher : type bs b m ms t h c. (bs,b,ms,m,t,h,c) constructor_arguments -> (ms,m,t) match_t -> (ms,t) compiled_match_t
  = fun a -> function
    | M f ->
        fun ~ok ~ko t state ->
          let state = ref state in
          let gls = ref [] in
          !state, f ~ok:(compile_matcher_ok a ok gls state)
                   ~ko:(compile_matcher_ko ko gls state) t, !gls
    | MS f -> f

let rec tyargs_of_args : type a b c d e. string -> (a,b,c,d,e) compiled_constructor_arguments -> (bool * string * string) list =
  fun self -> function
  | XN -> [false,self,""]
  | XA ({ ty },rest) -> (false,Conversion.show_ty_ast ty,"") :: tyargs_of_args self rest

let compile_constructors ty self self_name l =
  let names =
    List.fold_right (fun (K(name,_,_,_,_)) -> StrSet.add name) l StrSet.empty in
  if StrSet.cardinal names <> List.length l then
    anomaly ("Duplicate constructors name in ADT: " ^ Conversion.show_ty_ast ty);
  List.fold_left (fun (acc,sacc) (K(name,_,a,b,m)) ->
    let c = Global_symbols.declare_global_symbol name in
    let args = compile_arguments a self in
    Constants.Map.add c (XK(args,compile_builder a b,compile_matcher a m)) acc,
    StrMap.add name (tyargs_of_args self_name args) sacc)
      (Constants.Map.empty,StrMap.empty) l

let document_constructor fmt name doc argsdoc =
  Fmt.fprintf fmt "@[<hov2>type %s@[<hov>%a.%s@]@]@\n"
    name pp_ty_args argsdoc (if doc = "" then "" else " % " ^ doc)

let document_kind fmt = function
  | Conversion.TyApp(s,_,l) ->
      let n = List.length l + 2 in
      let l = Array.init n (fun _ -> "type") in
      Fmt.fprintf fmt "@[<hov 2>kind %s %s.@]@\n"
        s (String.concat " -> " (Array.to_list l))
  | Conversion.TyName s -> Fmt.fprintf fmt "@[<hov 2>kind %s type.@]@\n" s

let document_adt doc ty ks cks fmt () =
  if doc <> "" then
    begin pp_comment fmt ("% " ^ doc); Fmt.fprintf fmt "@\n" end;
  document_kind fmt ty;
  List.iter (fun (K(name,doc,_,_,_)) ->
    if name <> "uvar" then
      let argsdoc = StrMap.find name cks in
      document_constructor fmt name doc argsdoc) ks

let adt ~mkinterval ~look ~mkConst ~alloc ~mkUnifVar { ty; constructors; doc; pp } =
  let readback_ref = ref (fun ~depth _ _ _ _ -> assert false) in
  let embed_ref = ref (fun ~depth _ _ _ _ -> assert false) in
  let sconstructors_ref = ref StrMap.empty in
  let self = {
    ContextualConversion.ty;
    pp;
    pp_doc = (fun fmt () ->
      document_adt doc ty constructors !sconstructors_ref fmt ());
    readback = (fun ~depth hyps constraints state term ->
      !readback_ref ~depth hyps constraints state term);
    embed = (fun ~depth hyps constraints state term ->
      !embed_ref ~depth hyps constraints state term);
  } in
  let cconstructors, sconstructors = compile_constructors ty self (Conversion.show_ty_ast ty) constructors in
  sconstructors_ref := sconstructors;
  readback_ref := readback ~mkinterval ~look ~alloc ~mkUnifVar ty cconstructors;
  embed_ref := embed ~mkConst ty pp cconstructors;
  self

end

type declaration =
  | MLCode of t * doc_spec
  | MLData : 'a Conversion.t -> declaration
  | MLDataC : ('a,'h,'c) ContextualConversion.t -> declaration
  | LPDoc  of string
  | LPCode of string

(* doc *)
let ws_to_max fmt max n =
  if n < max then Format.fprintf fmt "%s" (String.make (max - n) ' ')
  else ()
let pp_tab_arg i max sep fmt (dir,ty,doc) =
  let dir = if dir then "i" else "o" in
  if i = 0 then Fmt.pp_set_tab fmt () else ();
  Fmt.fprintf fmt "%s:%s%s" dir ty sep;
  if i = 0 then (ws_to_max fmt max (String.length ty); Fmt.pp_set_tab fmt ()) else Fmt.pp_print_tab fmt ();
  if doc <> "" then begin Fmt.fprintf fmt " %% %s" doc end;
  Fmt.pp_print_tab fmt ()
;;

let pp_tab_args fmt l =
  let n = List.length l - 1 in
  let max = List.fold_left (fun m (_,s,_) -> max (String.length s) m) 0 l in
  Fmt.pp_open_tbox fmt ();
  if l = [] then Fmt.fprintf fmt ".";
  List.iteri (fun i x ->
    let sep = if i = n then "." else "," in
    pp_tab_arg i max sep fmt x) l;
  Fmt.pp_close_tbox fmt ()
;;

let pp_arg sep fmt (dir,ty,doc) =
  let dir = if dir then "i" else "o" in
  Fmt.fprintf fmt "%s:%s%s" dir ty sep
;;

let pp_args = pplist (pp_arg "") ", " ~pplastelem:(pp_arg "")

let pp_pred fmt docspec name doc_pred args =
  let args = List.rev args in
  match docspec with
  | DocNext ->
     Fmt.fprintf fmt "@[<v 2>external pred %s %% %s@;%a@]@."
       name doc_pred pp_tab_args args
  | DocAbove ->
    let doc =
       "[" ^ String.concat " " (name :: List.map (fun (_,_,x) -> x) args) ^
       "] " ^ doc_pred in
     Fmt.fprintf fmt "@[<v>%% %a@.external pred %s @[<hov>%a.@]@]@.@."
       pp_comment doc name pp_args args
;;

let pp_variadictype fmt name doc_pred ty args =
  let parens s = if String.contains s ' ' then "("^s^")" else s in
  let args = List.rev ((false,"variadic " ^ parens ty ^ " prop","") :: args) in
  let doc =
    "[" ^ String.concat " " (name :: List.map (fun (_,_,x) -> x) args) ^
    "...] " ^ doc_pred in
  Fmt.fprintf fmt "@[<v>%% %a@.external type %s@[<hov>%a.@]@]@.@."
        pp_comment doc name pp_ty_args args
;;

let document_pred fmt docspec name ffi =
  let rec doc
  : type i o h c. (bool * string * string) list -> (i,o,h,c) ffi -> unit
  = fun args -> function
    | In( { Conversion.ty }, s, ffi) -> doc ((true,Conversion.show_ty_ast ty,s) :: args) ffi
    | Out( { Conversion.ty }, s, ffi) -> doc ((false,Conversion.show_ty_ast ty,s) :: args) ffi
    | InOut( { Conversion.ty }, s, ffi) -> doc ((false,Conversion.show_ty_ast ty,s) :: args) ffi
    | CIn( { ContextualConversion.ty }, s, ffi) -> doc ((true,Conversion.show_ty_ast ty,s) :: args) ffi
    | COut( { ContextualConversion.ty }, s, ffi) -> doc ((false,Conversion.show_ty_ast ty,s) :: args) ffi
    | CInOut( { ContextualConversion.ty }, s, ffi) -> doc ((false,Conversion.show_ty_ast ty,s) :: args) ffi
    | Read (_,s) -> pp_pred fmt docspec name s args
    | Easy s -> pp_pred fmt docspec name s args
    | Full (_,s) -> pp_pred fmt docspec name s args
    | FullHO (_,s) -> pp_pred fmt docspec name s args
    | VariadicIn( _,{ ContextualConversion.ty }, s) -> pp_variadictype fmt name s (Conversion.show_ty_ast ty) args
    | VariadicOut( _,{ ContextualConversion.ty }, s) -> pp_variadictype fmt name s (Conversion.show_ty_ast ty) args
    | VariadicInOut( _,{ ContextualConversion.ty }, s) -> pp_variadictype fmt name s (Conversion.show_ty_ast ty) args
  in
    doc [] ffi
;;

let document fmt l calc_list =
  let omargin = Fmt.pp_get_margin fmt () in
  Fmt.pp_set_margin fmt 75;
  Fmt.fprintf fmt "@[<v>";
  Fmt.fprintf fmt "@\n@\n";
  List.iter (function
    | MLCode(Pred(name,ffi,_), docspec) ->
        document_pred fmt docspec name ffi;
        if name = "calc" then begin
          Format.fprintf fmt "%s@\n@\n" "%  --- Operators ---";
          List.iter (fun (_,x) -> Format.fprintf fmt "%s@\n@\n" x.CalcHooks.ty_decl ) calc_list
        end;
    | MLData { pp_doc } -> Fmt.fprintf fmt "%a@\n" pp_doc ()
    | MLDataC { pp_doc } -> Fmt.fprintf fmt "%a@\n" pp_doc ()
    | LPCode s -> Fmt.fprintf fmt "%s" s; Fmt.fprintf fmt "@\n@\n"
    | LPDoc s -> pp_comment fmt ("% " ^ s); Fmt.fprintf fmt "@\n@\n") l;
  Fmt.fprintf fmt "@\n@\n";
  Fmt.fprintf fmt "@]@.";
  Fmt.pp_set_margin fmt omargin
;;

type builtin_table = (int, t) Hashtbl.t
[@@deriving show]

end

type symbol_table = {
  mutable c2s : string Constants.Map.t;
  c2t : (constant, term) Hashtbl.t;
  mutable frozen_constants : int;
}
[@@deriving show]

type executable = {
  (* the lambda-Prolog program: an indexed list of clauses *) 
  compiled_program : prolog_prog;
  (* chr rules *)
  chr : CHR.t;
  (* query *)
  initial_depth : int; (* used by findall and CHR *)
  initial_goal: term;
  (* constraints coming from compilation *)
  initial_runtime_state : State.t;
  (* Hashconsed symbols + their string equivalent *)
  symbol_table : symbol_table;
  (* Indexed FFI entry points *)
  builtins : BuiltInPredicate.builtin_table;
  (* solution *)
  assignments : term Util.StrMap.t;
}

type pp_ctx = {
  uv_names : (string Util.IntMap.t * int) ref;
  table : symbol_table;
}

type solution = {
  assignments : term StrMap.t;
  constraints : constraints;
  state : State.t;
  pp_ctx : pp_ctx;
  state_for_relocation : int * symbol_table;
}
type 'a outcome = Success of solution | Failure | NoMoreSteps

exception CannotDeclareClauseForBuiltin of Loc.t option * constant
