(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

(* Internal term representation *)

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
      Fmt.fprintf f "%s:%4d:" (Filename.basename (Ploc.file_name x)) (Ploc.line_nb x));
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

module CD = struct
  let is_int = is_int
  let to_int = out_int
  let of_int x = CData (in_int x)

  let is_float = is_float
  let to_float = out_float
  let of_float x = CData (in_float x)

  let is_string = is_string
  let to_string x = F.show (out_string x)
  let of_string x = CData (in_string (F.from_string x))
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

  val ctypec : constant

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
   let xx = Const n in
   Hashtbl.add h' n ("frozen-"^string_of_int n);
   Hashtbl.add h'' n xx;
   n,xx)
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
let ctypec = fst (funct_of_ast F.ctypef)

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
          else if hd == C.andc then 110 
          else appl_prec in
         with_parens hdlvl (fun _ ->
          if hd == C.andc then
            pplist (aux inf_prec depth) ~pplastelem:(aux_last inf_prec depth) "," f (x::xs)
          else pp_app f ppconstant (aux inf_prec depth)
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

module CustomConstraints : sig
    type 'a constraint_type

    (* Must be purely functional *)
    val declare_constraint :
      name:string ->
      pp:(Fmt.formatter -> 'a -> unit) ->
      empty:'a ->
        'a constraint_type

     
    type state = Obj.t IM.t
    val update : state ref -> 'a constraint_type -> ('a -> 'a) -> unit
    val read : state ref -> 'a constraint_type -> 'a
  end = struct
    type 'a constraint_type = int
    type state = Obj.t IM.t
  let custom_constraints_declarations = ref IM.empty

    let cid = ref 0
    let declare_constraint ~name ~pp ~empty =
      incr cid;
      custom_constraints_declarations :=
        IM.add !cid (name,Obj.repr pp, Obj.repr empty) !custom_constraints_declarations;
      !cid

    let find custom_constraints id =
      try IM.find id !custom_constraints
      with Not_found ->
        let _, _, init = IM.find id !custom_constraints_declarations in
        init

    let update custom_constraints id f =
      custom_constraints :=
        IM.add id (Obj.repr (f (Obj.obj (find custom_constraints id)))) !custom_constraints
    let read custom_constraints id = Obj.obj (find custom_constraints id)
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
  src : (int * term) list;
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
    src : (int * term) list;
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
type program = {
  (* n of sigma/local-introduced variables *)
  query_depth : int;
  (* the lambda-Prolog program: an indexed list of clauses *) 
  prolog_program : prolog_prog [@printer (pp_extensible pp_prolog_prog)];
  (* constraint handling rules *)
  chr : chr [@printer (pp_extensible pp_chr)];
  modes : mode_decl C.Map.t; 

  (* extra stuff, for typing *)
  declared_types : (constant * int * term) list; (* name, nARGS, type *)
  clauses_w_info : (CData.t * string list * clause) list; (* loc, args names, clause *)
}
type query = string list * int * env * term

type prolog_prog += Index of idx
let () = extend_printer pp_prolog_prog (fun fmt -> function
  | Index _ -> Fmt.fprintf fmt "<prolog_prog>";`Printed
  | _ -> `Passed)
let wrap_prolog_prog x = Index x
let unwrap_prolog_prog = function Index x -> x | _ -> assert false

exception No_clause

(* vim: set foldmethod=marker: *)
