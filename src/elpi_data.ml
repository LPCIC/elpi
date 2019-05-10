(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* Internal term representation *)

module Fmt = Format
module F = Elpi_ast.Func
open Elpi_util

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

(* Used by pretty printers, to be later instantiated in module Constants *)
let pp_const = mk_extensible_printer ()
type constant = int (* De Bruijn levels *)
[@printer (pp_extensible pp_const)]
[@@deriving show, eq]

(* To be instantiated after the dummy term is defined *)
let pp_oref = mk_extensible_printer ()

let id_term = UUID.make ()
type view =
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
and term = view (* needed at the user-level API *)
and uvar_body = {
  mutable contents : term [@printer (pp_extensible_any ~id:id_term pp_oref)];
  mutable rest : stuck_goal list [@printer fun _ _ -> ()]
                                 [@equal fun _ _ -> true];
}
and stuck_goal = {
  mutable blockers : blockers;
  kind : stuck_goal_kind;
}
and blockers = uvar_body list
and stuck_goal_kind =
 | Constraint of constraint_def
 | Unification of unification_def 
and unification_def = {
  adepth : int;
  env : term array;
  bdepth : int;
  a : term;
  b : term;
  matching: bool;
}
and constraint_def = {
  cdepth : int;
  prog : prolog_prog [@equal fun _ _ -> true]
               [@printer (fun fmt _ -> Fmt.fprintf fmt "<prolog_prog>")];
  context : clause_src list;
  conclusion : term;
}
and clause_src = { hdepth : int; hsrc : term }
and prolog_prog = {
  src : clause_src list; (* hypothetical context in original form, for CHR *)
  index : index;
}
and index = second_lvl_idx Elpi_ptmap.t
and second_lvl_idx =
| TwoLevelIndex of {
    mode : mode;
    argno : int; 
    all_clauses : clause list;         (* when the query is flexible *)
    flex_arg_clauses : clause list;       (* when the query is rigid but arg_id ha nothing *)
    arg_idx : clause list Elpi_ptmap.t;   (* when the query is rigid (includes in each binding flex_arg_clauses) *)
  }
| BitHash of {
    mode : mode;
    args : int list;
    time : int; (* time is used to recover the total order *)
    args_idx : (clause * int) list Elpi_ptmap.t; (* clause, insertion time *)
  }
and clause = {
    depth : int;
    args : term list;
    hyps : term list;
    vars : int;
    mode : mode; (* CACHE to avoid allocation in get_clause *)
}
and mode = bool list (* true=input, false=output *)
[@@deriving show, eq]

type indexing =
  | MapOn of int
  | Hash of int list
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

  let loc = Elpi_ast.cloc
  let is_loc = loc.CData.isc
  let to_loc = loc.CData.cout
  let of_loc x = CData (loc.CData.cin x)

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
  val mkConst : constant -> term
  val show : constant -> string
  val pp : Fmt.formatter -> constant -> unit
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
  val asc      : constant
  val arrowc   : constant
  val uvarc    : constant

  val ctypec   : constant
  val prop     : term
  val variadic : constant
  val any      : term

  val spillc   : constant

  val declare_constraintc : constant
  val print_constraintsc  : constant
  (* }}} *)

  (* Value for unassigned UVar/Arg *)
  val dummy  : term

  type t = constant
  val compare : t -> t -> int

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t

  (* mkinterval d n 0 = [d; ...; d+n-1] *)
  val mkinterval : int -> int -> int -> term list

end = struct (* {{{ *)

(* Ast (functor name) -> negative int n (constant) * hashconsed (Const n) *)
let ast2ct : (F.t, constant * term) Hashtbl.t = Hashtbl.create 37
(* constant -> string *)
let c2s : (constant, string) Hashtbl.t = Hashtbl.create 37
(* constant n -> hashconsed (Const n) *)
let c2t : (constant, term) Hashtbl.t = Hashtbl.create 17

let fresh = ref 0

let funct_of_ast x =
  try Hashtbl.find ast2ct x
  with Not_found ->
    decr fresh;
    let n = !fresh in
    let xx = Const n in
    let p = n,xx in
    Hashtbl.add c2s n (F.show x);
    Hashtbl.add c2t n xx;
    Hashtbl.add ast2ct x p;
    p

let mkConst x =
  try Hashtbl.find c2t x
  with Not_found ->
    let xx = Const x in
    Hashtbl.add c2s x ("c" ^ string_of_int x);
    Hashtbl.add c2t x xx;
    xx
  [@@inline]

let show n =
   try Hashtbl.find c2s n
   with Not_found -> string_of_int n

let fresh () =
   decr fresh;
   let n = !fresh in
   let xx = Const n in
   Hashtbl.add c2s n ("frozen-" ^ string_of_int n);
   Hashtbl.add c2t n xx;
   n, xx

let pp fmt c = Fmt.fprintf fmt "%s" (show c)

let from_astc a = fst (funct_of_ast a)
let from_ast a = snd (funct_of_ast a)

let from_stringc s = from_astc F.(from_string s)
let from_string s = from_ast F.(from_string s)

let andc2 = from_astc F.andf2
let andc, andt = funct_of_ast F.andf
let arrowc = from_astc F.arrowf
let asc = from_stringc "as"
let consc, cons = funct_of_ast F.consf
let cutc, cut = funct_of_ast F.cutf
let entailsc = from_stringc "?-"
let eqc = from_astc F.eqf
let uvarc = from_stringc "uvar"
let implc = from_astc F.implf
let nablac = from_stringc "nabla"
let nilc, nil = funct_of_ast F.nilf
let orc = from_astc F.orf
let pic, pi = funct_of_ast F.pif
let rimplc, rimpl = funct_of_ast F.rimplf
let rulec = from_stringc "rule"
let sigmac = from_astc F.sigmaf
let spillc = from_astc (F.spillf)
let truec = from_ast F.truef

let ctypec = fst (funct_of_ast F.ctypef)
let prop = from_string "prop"
let variadic = from_stringc "variadic"
let any = from_string "any"

let declare_constraintc = from_stringc "declare_constraint"
let print_constraintsc = from_stringc "print_constraints"

let dummy = App (-9999,cut,[])

module Self = struct
  type t = constant
  let compare x y = x - y
  let pp = pp
  let show = show
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
 else mkConst (n+depth)::mkinterval depth argsno (n+1)
;;

end (* }}} *)

let mkConst x = Constants.mkConst x [@@inline]

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
    pattern : Constants.t list;
    rule_name : string
  }
  val pp_sequent : Fmt.formatter -> sequent -> unit
  val show_sequent : sequent -> string
  val pp_rule : Fmt.formatter -> rule -> unit
  val show_rule : rule -> string

  val empty : t

  val new_clique : constant list -> t -> t * clique
  val clique_of : constant -> t -> Constants.Set.t option
  val add_rule : clique -> rule -> t -> t
  
  val rules_for : constant -> t -> rule list

  val pp : Fmt.formatter -> t -> unit
  val show : t -> string

end = struct (* {{{ *)

  type sequent = { eigen : term; context : term; conclusion : term }
  and rule = {
    to_match : sequent list;
    to_remove : sequent list;
    patsno : int;
    guard : term option;
    new_goal : sequent option;
    nargs : int [@default 0];
    pattern : Constants.t list;
    rule_name : string;
  }
  [@@ deriving show]
  type t = {
    cliques : Constants.Set.t Constants.Map.t;
    rules : rule list Constants.Map.t
  }
  [@@ deriving show]
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

module CustomState : sig
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
    val pp : Fmt.formatter -> t -> unit
     
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

(* An elpi program, as parsed.  But for idx and query_depth that are threaded
   around in the main loop, chr and modes are globally stored in Constraints
   and Clausify. *)
type clause_w_info = {
  clloc : CData.t;
  clargsname : string list;
  clbody : clause;
}
[@@ deriving show]

type macro_declaration = (Elpi_ast.Term.t * Loc.t) F.Map.t
[@@ deriving show]

(* This is paired with a pre-stack term, i.e. a stack term where args are
 * represented with constants as "%Arg3" *)
type argmap = {
  nargs : int;
  c2i : int Constants.Map.t;
  i2n : string IntMap.t;
  n2t : term StrMap.t;
  n2i : int StrMap.t;
}
[@@ deriving show]

let empty_amap = {
 nargs = 0;
 c2i = Constants.Map.empty;
 i2n = IntMap.empty;
 n2t = StrMap.empty;
 n2i = StrMap.empty;
}

let mk_Arg n { c2i; nargs; i2n; n2t; n2i } =
  let cname = Printf.sprintf "%%Arg%d" nargs in
  let n' = Constants.from_string cname in
  let nc = Constants.from_stringc cname in
  let i2n = IntMap.add nargs n i2n in
  let c2i = Constants.Map.add nc nargs c2i in
  let n2t = StrMap.add n n' n2t in
  let n2i = StrMap.add n nargs n2i in
  let nargs = nargs + 1 in
  { c2i; nargs; i2n; n2t; n2i }, (n', nc)

type preterm = {
  term : term; (* Args are still constants *)
  amap : argmap;
  loc : Loc.t
}
[@@ deriving show]

type type_declaration = {
  tname : constant;
  ttype : preterm;
}
[@@ deriving show]

type presequent = {
  peigen : term;
  pcontext : term;
  pconclusion : term;
}
[@@ deriving show]
type prechr_rule = {
  pto_match : presequent list;
  pto_remove : presequent list;
  pguard : term option;
  pnew_goal : presequent option;
  pamap : argmap;
  pname : string;
  pifexpr : string option;
  pcloc : Loc.t;
}
[@@ deriving show]

let todopp fmt _ = error "not implemented"

type executable = {
  (* the lambda-Prolog program: an indexed list of clauses *) 
  compiled_program : prolog_prog;
  (* chr rules *)
  chr : CHR.t;
  (* initial depth (used for both local variables and CHR (#eigenvars) *)
  initial_depth : int;
  (* query *)
  initial_goal: term;
  (* constraints coming from compilation *)
  initial_state : CustomState.t;
  (* solution *)
  assignments : term StrMap.t;
}

exception No_clause
exception No_more_steps

type custom_state = CustomState.t
type constraints = stuck_goal list

type solution = {
  assignments : term StrMap.t;
  constraints : constraints;
  state : custom_state;
}
type outcome = Success of solution | Failure | NoMoreSteps

type hyps = clause_src list

(* Built-in predicates and their FFI *************************************** *)

(* (depth:int -> hyps -> solution -> term list -> term list * custom_state) *)

module Builtin = struct

type name = string
type doc = string

type ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list

let rec show_ty_ast ?(outer=true) = function
  | TyName s -> s
  | TyApp (s,x,xs) ->
      let t = String.concat " " (s :: List.map (show_ty_ast ~outer:false) (x::xs)) in
      if outer then t else "("^t^")"

type 'a oarg = Keep | Discard
type 'a ioarg = Data of 'a | NoData

exception TypeErr of ty_ast * term

type extra_goals = term list

type 'a embedding =
  depth:int -> hyps -> solution -> 'a -> custom_state * term * extra_goals
type 'a readback =
  depth:int -> hyps -> solution -> term -> custom_state * 'a

type 'a data = {
  ty : ty_ast;
  doc : doc;
  embed : 'a embedding;   (* 'a -> term *)
  readback : 'a readback; (* term -> 'a *)
}

type ('function_type, 'inernal_outtype_in) ffi =
  | In   : 't data * doc * ('i, 'o) ffi -> ('t -> 'i,'o) ffi
  | Out  : 't data * doc * ('i, 'o * 't option) ffi -> ('t oarg -> 'i,'o) ffi
  | InOut  : 't data * doc * ('i, 'o * 't option) ffi -> ('t ioarg -> 'i,'o) ffi
  | Easy : doc -> (depth:int -> 'o, 'o) ffi
  | Read : doc -> (depth:int -> hyps -> solution -> 'o, 'o) ffi
  | Full : doc -> (depth:int -> hyps -> solution -> custom_state * 'o, 'o) ffi
  | VariadicIn : 't data * doc -> ('t list -> depth:int -> hyps -> solution -> custom_state * 'o, 'o) ffi
  | VariadicOut : 't data * doc -> ('t oarg list -> depth:int -> hyps -> solution -> custom_state * ('o * 't option list option), 'o) ffi
  | VariadicInOut : 't data * doc -> ('t ioarg list -> depth:int -> hyps -> solution -> custom_state * ('o * 't option list option), 'o) ffi

type t = Pred : name * ('a,unit) ffi * 'a -> t

type doc_spec = DocAbove | DocNext

module ADT = struct

type ('matched, 't) match_t =
  ok:'matched ->
  ko:(solution -> custom_state * term * extra_goals) ->
  't -> solution -> custom_state * term * extra_goals

type ('b,'m,'t) constructor_arguments =
  | N : ('t,solution -> custom_state * term * extra_goals, 't) constructor_arguments
  | A : 'a data * ('b,'m,'t) constructor_arguments -> ('a -> 'b, 'a -> 'm, 't) constructor_arguments
  | S : ('b,'m,'t) constructor_arguments -> ('t -> 'b, 't -> 'm, 't) constructor_arguments
    
type 't constructor =
  K : string * doc *
      ('build_t,'matched_t,'t) constructor_arguments *
      'build_t * ('matched_t,'t) match_t
    -> 't constructor

type 't adt = {
  ty : ty_ast;
  doc : doc;
  constructors : 't constructor list;
}

type 't compiled_constructor =
    CK : ('build_t,'matched_t,'t) constructor_arguments *
    'build_t * ('matched_t,'t) match_t
  -> 't compiled_constructor

type 't compiled_adt = ('t compiled_constructor) Constants.Map.t

let rec readback_args : type a m t.
  look:(depth:int -> term -> term) ->
  ty_ast -> t compiled_adt -> depth:int -> hyps -> solution -> term ->
  (a,m,t) constructor_arguments -> a -> term list ->
    custom_state * t
= fun ~look ty adt ~depth hyps solution origin args convert l ->
    match args, l with
    | N, [] -> solution.state, convert
    | N, _ -> raise (TypeErr(ty,origin))
    | A _, [] -> assert false
    | S _, [] -> assert false
    | A(d,rest), x::xs ->
      let state, x = d.readback ~depth hyps solution x in
      readback_args ~look ty adt ~depth hyps { solution with state } origin
        rest (convert x) xs
    | S rest, x::xs ->
      let state, x = readback ~look ty adt ~depth hyps solution x in
      readback_args ~look ty adt ~depth hyps { solution with state } origin
        rest (convert x) xs

and readback : type t.
  look:(depth:int -> term -> term) ->
  ty_ast -> t compiled_adt -> depth:int -> hyps -> solution -> term ->
    custom_state * t
= fun ~look ty adt ~depth hyps sol t ->
  try match look ~depth t with
  | Const c ->
      let CK(args,read,_) = Constants.Map.find c adt in
      readback_args ~look ty adt ~depth hyps sol t args read []
  | App(c,x,xs) ->
      let CK(args,read,_) = Constants.Map.find c adt in
      readback_args ~look ty adt ~depth hyps sol t args read (x::xs)
  | _ -> raise (TypeErr(ty,t))
  with Not_found -> raise (TypeErr(ty,t))

;;

let build kname = function
| [] -> mkConst kname
| x :: xs -> mkApp kname x xs

let rec adt_embed_args : type m a t.
  ty_ast -> t compiled_adt -> constant ->
  depth:int -> hyps ->
  (a,m,t) constructor_arguments ->
  (solution -> custom_state * term * extra_goals) list ->
    m
= fun ty adt kname ~depth hyps args acc ->
    match args with
    | N -> fun sol ->
        let sol, ts, gls =
          List.fold_left (fun (sol,acc,gls) f ->
            let state, t, goals = f sol in
            { sol with state }, t :: acc, goals :: gls)
            (sol,[],[]) acc in
        sol.state, build kname ts, List.(flatten gls)
    | A(d,args) ->
        fun x ->
          adt_embed_args ty adt kname ~depth hyps
            args ((fun sol -> d.embed ~depth hyps sol x) :: acc)
    | S args ->
        fun x ->
          adt_embed_args ty adt kname ~depth hyps
            args ((fun sol -> embed ty adt ~depth hyps sol x) :: acc)

and embed : type a.
  ty_ast -> a compiled_adt ->
  depth:int -> hyps -> solution ->
    a -> custom_state * term * extra_goals
= fun ty adt ->
  let bindings = Constants.Map.bindings adt in
  fun ~depth hyps sol t ->
    let rec aux l sol =
      match l with
      | [] -> Elpi_util.type_error
                  ("Pattern matching failure embedding: " ^ show_ty_ast ty)
      | (kname, CK(args,_,matcher)) :: rest ->
        let ok = adt_embed_args ty adt kname ~depth hyps args [] in
        matcher ~ok ~ko:(aux rest) t sol in
     aux bindings sol
;;

let compile_constructors ty l =
  let open Elpi_util in
  let names =
    List.fold_right (fun (K(name,_,_,_,_)) -> StrSet.add name) l StrSet.empty in
  if StrSet.cardinal names <> List.length l then
    anomaly ("Duplicate constructors name in ADT: " ^ show_ty_ast ty);
  List.fold_left (fun acc (K(name,_,a,b,m)) ->
    Constants.(Map.add (from_stringc name) (CK(a,b,m)) acc))
      Constants.Map.empty l

end

type declaration =
  | MLCode of t * doc_spec
  | MLADT : 'a ADT.adt -> declaration
  | MLCData : 'a data * 'a CData.cdata -> declaration
  | LPDoc  of string
  | LPCode of string

let register, lookup, all =
 (* Must either raise No_clause or succeed with the list of new goals *)
 let builtins : (int, t) Hashtbl.t = Hashtbl.create 17 in
 let check (Pred(s,_,_)) = 
    if s = "" then
      anomaly ("Built-in predicate name must be non empty");
    let idx = Constants.from_stringc s in
    if Hashtbl.mem builtins idx then
      anomaly ("Duplicate built-in predicate name " ^ s);
    idx in
 (fun b ->
    let idx = check b in
    Hashtbl.add builtins idx b),
 Hashtbl.find builtins,
 (fun () -> Hashtbl.fold (fun k _ acc -> k::acc) builtins [])
;;

let is_declared x =
  (try let _f = lookup x in true
   with Not_found -> false)
  || x == Constants.declare_constraintc
  || x == Constants.print_constraintsc
  || x == Constants.cutc
;;

let from_builtin_name x =
  let c = Constants.from_stringc x in
  if not (is_declared c) then error ("No builtin called " ^ x);
  c

(* doc *)
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

let pp_tab_arg i sep fmt (dir,ty,doc) =
  let dir = if dir then "i" else "o" in
  if i = 0 then Fmt.pp_set_tab fmt () else ();
  Fmt.fprintf fmt "%s:%s%s" dir ty sep;
  if i = 0 then Fmt.pp_set_tab fmt () else Fmt.pp_print_tab fmt ();
  if doc <> "" then begin Fmt.fprintf fmt " %% %s" doc end;
  Fmt.pp_print_tab fmt ()
;;

let pp_tab_args fmt l =
  let n = List.length l - 1 in
  Fmt.pp_open_tbox fmt ();
  List.iteri (fun i x ->
    let sep = if i = n then "." else "," in
    pp_tab_arg i sep fmt x) l;
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

let pp_ty sep fmt (_,s,_) = Fmt.fprintf fmt " %s%s" s sep
let pp_ty_args = pplist (pp_ty "") " ->" ~pplastelem:(pp_ty "")

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
  : type i o. (bool * string * string) list -> (i,o) ffi -> unit
  = fun args -> function
    | In( { ty }, s, ffi) -> doc ((true,show_ty_ast ty,s) :: args) ffi
    | Out( { ty }, s, ffi) -> doc ((false,show_ty_ast ty,s) :: args) ffi
    | InOut( { ty }, s, ffi) -> doc ((false,show_ty_ast ty,s) :: args) ffi
    | Read s -> pp_pred fmt docspec name s args
    | Easy s -> pp_pred fmt docspec name s args
    | Full s -> pp_pred fmt docspec name s args
    | VariadicIn( { ty }, s) -> pp_variadictype fmt name s (show_ty_ast ty) args
    | VariadicOut( { ty }, s) -> pp_variadictype fmt name s (show_ty_ast ty) args
    | VariadicInOut( { ty }, s) -> pp_variadictype fmt name s (show_ty_ast ty) args
  in
    doc [] ffi
;;

let rec tyargs_of_args : type a b c. string -> (a,b,c) ADT.constructor_arguments -> (bool * string * string) list =
  fun self -> function
  | ADT.N -> [false,self,""]
  | ADT.A ({ ty },rest) -> (false,show_ty_ast ty,"") :: tyargs_of_args self rest
  | ADT.S rest -> (false,self,"") :: tyargs_of_args self rest

let document_constructor fmt self (ADT.K(name,doc,args,_,_)) =
  let args = tyargs_of_args self args in
  Fmt.fprintf fmt "@[<hov2>type %s@[<hov>%a.%s@]@]@\n"
    name pp_ty_args args (if doc = "" then "" else " % " ^ doc)

let document_kind fmt = function
  | TyApp(s,_,l) ->
      let n = List.length l + 2 in
      let l = Array.init n (fun _ -> "type") in
      Fmt.fprintf fmt "@[<hov 2>kind %s %s.@]@\n"
        s (String.concat " -> " (Array.to_list l))
  | TyName s -> Fmt.fprintf fmt "@[<hov 2>kind %s type.@]@\n" s

let document_adt fmt ty ks =
  document_kind fmt ty;
  List.iter (document_constructor fmt (show_ty_ast ty)) ks

let document fmt l =
  let omargin = Fmt.pp_get_margin fmt () in
  Fmt.pp_set_margin fmt 75;
  Fmt.fprintf fmt "@[<v>";
  Fmt.fprintf fmt "@\n@\n";
  List.iter (function
    | MLCode(Pred(name,ffi,_), docspec) -> document_pred fmt docspec name ffi
    | MLCData ({ ty = TyName name; doc }, { name = c }) when name.[0] = '@' ->
        if doc <> "" then begin
          pp_comment fmt ("% " ^ doc); Fmt.fprintf fmt "@\n";
        end;
        (* TODO: use typeabbrv *)
        Fmt.fprintf fmt "@[<hov 2>macro %s :- ctype \"%s\".@]@\n@\n" name c;
    | MLCData ({ ty }, { name }) ->
        anomaly ("Cannot document " ^ show_ty_ast ty ^ " as a CData");
    | MLADT { ADT.doc; ty; constructors } ->
        if doc <> "" then begin
          pp_comment fmt ("% " ^ doc); Fmt.fprintf fmt "@\n";
        end;
        document_adt fmt ty constructors; Fmt.fprintf fmt "@\n"
    | LPCode s -> Fmt.fprintf fmt "%s" s; Fmt.fprintf fmt "@\n@\n"
    | LPDoc s -> pp_comment fmt ("% " ^ s); Fmt.fprintf fmt "@\n@\n") l;
  Fmt.fprintf fmt "@\n@\n";
  Fmt.fprintf fmt "@]@.";
  Fmt.pp_set_margin fmt omargin
;;

end

let of_term x = x

(* vim: set foldmethod=marker: *)
