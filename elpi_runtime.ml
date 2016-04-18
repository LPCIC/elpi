(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Fmt = Format
module F = Elpi_ast.Func

module Utils : sig

  val pplist : ?max:int -> ?boxed:bool ->
    (Fmt.formatter -> 'a -> unit) ->
    ?pplastelem:(Fmt.formatter -> 'a -> unit) ->
      string -> Fmt.formatter -> 'a list -> unit

  val smart_map : ('a -> 'a) -> 'a list -> 'a list

  (* tail rec when the two lists have len 1; raises no exception. *)
  val for_all2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
  val for_all3b : ('a -> 'a -> bool -> bool) -> 'a list -> 'a list -> bool list -> bool -> bool

  (*uses physical equality and calls anomaly if the element is not in the list*)
  val remove_from_list : 'a -> 'a list -> 'a list

  (*uses physical equality; does nothing if the element is not in the list*)
  val remove_from_list' : 'a -> ('a * 'b) list -> ('a * 'b) list

  (* returns Some t where f x = Some t for the first x in the list s.t.
     f x <> None; returns None if for every x in the list, f x = None *)
  val map_exists : ('a -> 'b option) -> 'a list -> 'b option

  val partition_i : (int -> 'a -> bool) -> 'a list -> 'a list * 'a list

  (* A regular error *)
  val error : string -> 'a

  (* An invariant is broken, i.e. a bug *)
  val anomaly : string -> 'a
  
  (* If we type check the program, then these are anomalies *)
  val type_error : string -> 'a

  val option_get : 'a option -> 'a

  val option_map : ('a -> 'b) -> 'a option -> 'b option

  (* of course we don't fork, we just swap sets of local refs *)
  module Fork : sig

    type 'a local_ref = 'a ref

    val new_local : 'a -> 'a local_ref

    type process = {
      (* To run a function in the child process *)
      exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;

      (* To get/set values from the memory of the child *)
      get : 'a. 'a local_ref -> 'a;
      set : 'a. 'a local_ref -> 'a -> unit
    }
    
    val fork : unit -> process

  end

end = struct (* {{{ *)

module Global: sig
 
   type backup

   (* Takes the initial value *)
   val new_local : 'a -> 'a ref
   val backup : unit -> backup
   val restore : backup -> unit

   (* Like doing a backup just after having created all globals *)
   val initial_backup : unit -> backup
  
   (* Hack, in case the initial value cannot be provided when the
    * global is created *) 
   val set_value : 'a ref -> 'a -> backup -> backup
   val get_value : 'a ref -> backup -> 'a

end = struct

type backup = (Obj.t ref * Obj.t) list

let all_globals : backup ref = ref []

let new_local (t : 'a) : 'a ref =
  let res = ref t in
  all_globals := Obj.magic (res,t) :: !all_globals;
  res

let set_value (g : 'a ref) (v : 'a) (l : (Obj.t ref * Obj.t) list) =
  let v = Obj.repr v in
  let g :Obj.t ref = Obj.magic g in
    List.map
      (fun (g',_ as orig) -> if g == g' then (g,v) else orig)
      l

let get_value (p : 'a ref) (l : (Obj.t ref * Obj.t) list) : 'a =
  Obj.magic (List.assq (Obj.magic p) l)

let backup () : (Obj.t ref * Obj.t) list =
  List.map (fun (o,_) -> o,!o) !all_globals

let restore l = List.iter (fun (r,v) -> r := v) l

let initial_backup () = !all_globals

end

module Fork = struct
  type 'a local_ref = 'a ref

  type process = {
    exec : 'a 'b. ('a -> 'b) -> 'a -> 'b;
    get : 'a. 'a local_ref -> 'a;
    set : 'a. 'a local_ref -> 'a -> unit
  }
    
  let new_local = Global.new_local
  let fork () =
    let saved_globals = Global.backup () in 
    let my_globals = ref (Global.initial_backup ()) in
    let ensure_runtime f x =
      Global.restore !my_globals;
      try
       let rc = f x in
       my_globals := Global.backup ();
       Global.restore saved_globals;
       rc
      with e ->
       my_globals := Global.backup ();
       Global.restore saved_globals;
       raise e in
    { exec = ensure_runtime;
      get = (fun p -> Global.get_value p !my_globals);
      set = (fun p v -> my_globals := Global.set_value p v !my_globals) }
          
end

let pplist ?(max=max_int) ?(boxed=false) ppelem ?(pplastelem=ppelem) sep f l =
 if l <> [] then begin
  if boxed then Fmt.fprintf f "@[<hov 1>";
  let args,last = match List.rev l with
    [] -> assert false;
  | head::tail -> List.rev tail,head in
  List.iteri (fun i x -> if i = max + 1 then Fmt.fprintf f "..."
                         else if i > max then ()
                         else Fmt.fprintf f "%a%s@ " ppelem x sep) args;
  Fmt.fprintf f "%a" pplastelem last;
  if boxed then Fmt.fprintf f "@]"
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

let rec for_all3b p l1 l2 bl b =
  match (l1, l2, bl) with
  | ([], [], _) -> true
  | ([a1], [a2], []) -> p a1 a2 b
  | ([a1], [a2], b3::_) -> p a1 a2 b3
  | (a1::l1, a2::l2, []) -> p a1 a2 b && for_all3b p l1 l2 bl b
  | (a1::l1, a2::l2, b3::bl) -> p a1 a2 b3 && for_all3b p l1 l2 bl b
  | (_, _, _) -> false
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


let option_get = function Some x -> x | None -> assert false
let option_map f = function Some x -> Some (f x) | None -> None

let remove_from_list x =
 let rec aux acc =
  function
     [] -> anomaly "Element to be removed not in the list"
   | y::tl when x==y -> List.rev acc @ tl
   | y::tl -> aux (y::acc) tl
 in
  aux []

let remove_from_list' x l =
 let rec aux acc =
  function
     [] -> l
   | (y,_)::tl when x==y -> List.rev acc @ tl
   | y::tl -> aux (y::acc) tl
 in
  aux [] l

let rec map_exists f =
 function
    [] -> None
  | hd::tl -> match f hd with None -> map_exists f tl | res -> res


let partition_i f l =
  let rec aux n a1 a2 = function
    | [] -> List.rev a1, List.rev a2
    | x :: xs ->
       if (f n x) then aux (n+1) (x::a1) a2 xs else aux (n+1) a1 (x::a2) xs
  in
    aux 0 [] [] l
;;

end (* }}} *)
open Utils


(* TODOS:
   - There are a few TODOs with different implementative choices to
     be benchmarked *)

let show_const = ref (fun _ -> assert false)

(* Invariant: a Heap term never points to a Query term *)
type constant = int (* De Brujin levels *)
[@printer fun fmt x -> Fmt.fprintf fmt "\"%s\"" (!show_const x)]
[@@deriving show, eq]
type term =
  (* Pure terms *)
  | Const of constant
  | Lam of term
  | App of constant * term * term list
  (* Clause terms: unif variables used in clauses *)
  | Arg of (*id:*)int * (*argsno:*)int
  | AppArg of (*id*)int * term list
  (* Heap terms: unif variables in the query *)
  | UVar of term attributed_ref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term attributed_ref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | String of F.t
  | Int of int
  | Float of float
and 'a attributed_ref = {
  mutable contents : 'a [@printer fun _ _ -> ()];
  mutable rest : constraint_ list [@printer fun _ _ -> ()] [@equal fun _ _ -> true];
}
and constraint_ =
 (* exn is the constraint;
    the associated list is the list of variables the constraint is
    associated to *)
  cstr * term attributed_ref list (* well... open type in caml < 4.02 *)
and cstr =
 | Delayed_goal of dg
 | Delayed_unif of int * term array * int * term * term
and dg = { depth : int;
           prog : block [@equal fun _ _ -> true];
           pdiff : (int * term) list;
           goal : term }
and block = int
[@@deriving show,eq]
and mode = bool list [@@deriving show]

let no_mode = []

type md = Mono of mode | Multi of (constant * (constant * constant) list) list

let destConst = function Const x -> x | _ -> assert false

let (!!) { contents = x } = x

module Constants : sig

  val funct_of_ast : F.t -> constant * term
  val constant_of_dbl : constant -> term
  val string_of_constant : constant -> string
  val new_fresh_constant : unit -> constant * term
 
  (* To keep the type of terms small, we use special constants for ! = pi.. *)
  val cutc   : term
  val truec  : term
  val andc   : constant
  val andc2  : constant
  val orc    : constant
  val implc  : constant
  val rimplc  : constant
  val pic    : constant
  val sigmac : constant
  val eqc    : constant
  val rulec : constant
  val consc  : constant
  val nilc   : term
  val entailsc : constant
  val nablac : constant
  val uvc : constant
  val asc : constant
  val letc : constant

  (* Value for unassigned UVar/Arg *)
  val dummy  : term

  type t = constant
  val compare : t -> t -> int

end = struct (* {{{ *)

(* Hash re-consing :-( *)
let funct_of_ast, constant_of_dbl, string_of_constant, new_fresh_constant =
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

let cutc = snd (funct_of_ast F.cutf)
let truec = snd (funct_of_ast F.truef)
let andc = fst (funct_of_ast F.andf)
let andc2 = fst (funct_of_ast F.andf2)
let orc = fst (funct_of_ast F.orf)
let implc = fst (funct_of_ast F.implf)
let rimplc = fst (funct_of_ast F.rimplf)
let pic = fst (funct_of_ast F.pif)
let sigmac = fst (funct_of_ast F.sigmaf)
let eqc = fst (funct_of_ast F.eqf)
let rulec = fst (funct_of_ast (F.from_string "rule"))
let nilc = snd (funct_of_ast F.nilf)
let consc = fst (funct_of_ast F.consf)
let nablac = fst (funct_of_ast (F.from_string "nabla"))
let entailsc = fst (funct_of_ast (F.from_string "?-"))
let uvc = fst (funct_of_ast (F.from_string "??"))
let asc = fst (funct_of_ast (F.from_string "as"))
let letc = fst (funct_of_ast (F.from_string ":="))

let dummy = App (-9999,cutc,[])

type t = constant
let compare = compare

end (* }}} *)
open Constants

let () = show_const := string_of_constant;;

(* mkinterval d n 0 = [d; ...; d+n-1] *)
let rec mkinterval depth argsno n =
 if n = argsno then []
 else constant_of_dbl (n+depth)::mkinterval depth argsno (n+1)
;;

module Pp : sig
 
  (* Low level printing *)
  val ppterm :
    constant -> string list ->
    constant -> term array ->
      Fmt.formatter -> term -> unit

  (* For user consumption *)
  val uppterm :
    constant -> string list ->
    constant -> term array ->
      Fmt.formatter -> term -> unit

  val do_deref : (?avoid:term attributed_ref -> from:int -> to_:int -> int -> term -> term) ref
  val do_app_deref : (?avoid:term attributed_ref -> from:int -> to_:int -> term list -> term -> term) ref

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
  let ppconstant f c = Fmt.fprintf f "%s" (string_of_constant c) in
  let rec pp_uvar prec depth vardepth args f r =
   if !!r == dummy then begin
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
   if try env.(n) == dummy with Invalid_argument _ -> true then
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
      UVar (r,vardepth,terms) when !!r != dummy -> 
       flat_cons_to_list depth acc
        (!do_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) when !!r != dummy -> 
       flat_cons_to_list depth acc
        (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | App (hd,x,[y]) when hd==consc -> flat_cons_to_list depth (x::acc) y
    | _ -> List.rev acc, t
  and is_lambda depth =
   function
      Lam _ -> true
    | UVar (r,vardepth,terms) when !!r != dummy ->
       is_lambda depth (!do_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) when !!r != dummy -> 
       is_lambda depth (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | _ -> false
  and aux_last prec depth f t =
   if nice then begin
   match t with
     Lam _ -> aux min_prec depth f t
   | UVar (r,vardepth,terms) when !!r != dummy -> 
      aux_last prec depth f (!do_deref ~from:vardepth ~to_:depth terms !!r)
   | AppUVar (r,vardepth,terms) when !!r != dummy -> 
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
   | t when nice &&
      match t with App (hd,_,_) when hd==consc -> true | _ -> t==nilc
     ->
      let prefix,last = flat_cons_to_list depth [] t in
      Fmt.fprintf f "[" ;
      pplist (aux Elpi_parser.list_element_prec depth) "," f prefix ;
      if last!=nilc then begin
       Fmt.fprintf f " | " ;
       aux prec 1 f last
      end;   
      Fmt.fprintf f "]"
    | Const s -> ppconstant f s 
    | App (hd,x,xs) ->
       (try
         let assoc,hdlvl =
          Elpi_parser.precedence_of (F.from_string (string_of_constant hd)) in
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
       let args = List.map destConst (mkinterval vardepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        Fmt.fprintf f "." ;
        pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant (r,args))
    | UVar (r,vardepth,argsno) when !!r == dummy ->
       let diff = vardepth - depth0 in
       let diff = if diff >= 0 then diff else 0 in
       let vardepth = vardepth - diff in
       let argsno = argsno + diff in
       let args = List.map destConst (mkinterval vardepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant (r,args))
    | UVar (r,vardepth,argsno) ->
       pp_uvar prec depth vardepth argsno f r
    | AppUVar (r,vardepth,terms) when !!r != dummy && nice -> 
       aux prec depth f (!do_app_deref ~from:vardepth ~to_:depth terms !!r)
    | AppUVar (r,vardepth,terms) -> 
       with_parens appl_prec (fun _ ->
        pp_app f (pp_uvar inf_prec depth vardepth 0) (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (r,terms))
    | Arg (n,argsno) ->
       let args = List.map destConst (mkinterval argsdepth argsno 0) in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        pp_app f (pp_arg prec depth) ppconstant (n,args))
    | AppArg (v,terms) ->
       with_parens appl_prec (fun _ ->
        pp_app f (pp_arg inf_prec depth) (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (v,terms))
    | Lam t ->
       with_parens lam_prec (fun _ ->
        let c = constant_of_dbl depth in
        Fmt.fprintf f "%a \\@ %a" (aux inf_prec depth) c
         (aux min_prec (depth+1)) t)
    | String str -> Fmt.fprintf f "\"%s\"" (F.show str)
    | Int i -> Fmt.fprintf f "%d" i
    | Float x -> Fmt.fprintf f "%f" x
  in
    try aux min_prec depth0 f t with e -> Fmt.fprintf f "EXN PRINTING: %s" (Printexc.to_string e)
;;

let ppterm = xppterm ~nice:false
let uppterm = xppterm ~nice:true

end (* }}} *)
open Pp

type trail_item =
   Assign of term attributed_ref
 | AddConstr of constraint_
 | DelConstr of constraint_

type trail = trail_item list ref
let trail : trail = Fork.new_local []
let last_call = Fork.new_local false;;
let delayed = Fork.new_local []
let new_delayed = Fork.new_local []
let to_resume = Fork.new_local []

module CMap = Map.Make(Constants)

let modes = Fork.new_local CMap.empty

type 'key clause =
  { depth : int; args : term list; hyps : term list; vars : int; key : 'key; mode: mode }

module CSet = Set.Make(Constants)

module CHR : sig

  type 'key t
  type clique

  val empty : 'key t

  val new_clique : constant list -> 'key t -> 'key t * clique
  val clique_of : constant -> 'key t -> CSet.t
  val add_rule : clique -> 'key clause -> 'key t -> 'key t
  
  val rules_for : constant -> 'key t -> 'key clause list

end = struct (* {{{ *)

  module CM = Map.Make(Constants)
  module RM = Map.Make(Constants)

  type 'a t = { cliques : CSet.t CM.t; rules : 'a clause list RM.t }
  type clique = CSet.t

  let empty = { cliques = CM.empty; rules = RM.empty }

  let new_clique cl ({ cliques } as chr) =
    if cl = [] then error "empty clique";
    let c = List.fold_right CSet.add cl CSet.empty in
    if CM.exists (fun _ c' -> not (CSet.is_empty (CSet.inter c c'))) cliques then
            error "overlapping constraint cliques";
    let cliques =
      List.fold_right (fun x cliques -> CM.add x c cliques) cl cliques in
    { chr with cliques }, c

  let clique_of c { cliques } =
    try CM.find c cliques with Not_found -> CSet.empty

  let add_rule cl r ({ rules } as chr) =
    let rules = CSet.fold (fun c rules ->
      try      
        let rs = RM.find c rules in
        RM.add c (rs @ [r]) rules
      with Not_found -> RM.add c [r] rules)
      cl rules in
    { chr with rules }


  let rules_for c { rules } =
    try RM.find c rules
    with Not_found -> []

end (* }}} *)

let add_constraint0 (_,vars as cstr) =
 delayed := cstr :: !delayed;
 List.iter (fun r -> r.rest <- cstr :: r.rest) vars

let print_cstr = ref (fun _ -> assert false);; 

let add_constraint cstr =
  (*!print_cstr cstr ;*)
  add_constraint0 cstr ;
  (match cstr with
      Delayed_unif _,_ -> ()
    | _ (* Delayed_goal _ *) ->
   [%spy "delay-add" (fun fmt _ -> Fmt.fprintf fmt "added") ()];
       new_delayed := (cstr, 0) :: !new_delayed);
  if not !last_call then trail := AddConstr cstr :: !trail

let remove_constraint0 (_,vars as cstr) =
        [%spy "delay-remove" (fun fmt -> Fmt.fprintf fmt "%a" pp_constraint_) cstr];
 delayed := remove_from_list cstr !delayed;
 List.iter (fun r -> r.rest <- remove_from_list cstr r.rest) vars

let remove_constraint cstr =
 remove_constraint0 cstr ;
 (match cstr with
     Delayed_unif _,_ -> ()
   | _ (* Delayed_goal _ *) ->
      new_delayed := remove_from_list' cstr !new_delayed);
 if not !last_call then trail := DelConstr cstr :: !trail
;;

let (@:=) r v =
  if r.rest <> [] then
    begin
     (*Fmt.fprintf Fmt.std_formatter
       "@[<hov 2>%d delayed goal(s) to resume since@ %a <-@ %a@]@\n%!"
          (List.length r.rest)
          (ppterm 0 [] 0 empty_env) (UVar(r,0,0))
          (ppterm 0 [] 0 empty_env) v;*)
     to_resume := r.rest @ !to_resume
    end;
 r.contents <- v
;;

let oref x = { contents = x; rest = [] }


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
 | AppUVar (r,_,_)::_ when !!r != dummy ->
     anomaly "non dereferenced terms in in_fragment"
*)
 | _ -> raise NotInTheFragment

exception NonMetaClosed

let deterministic_restriction e ~args_safe t =
 let rec aux =
  function
    Lam f -> aux f
  | App (_,t,l) -> aux t; List.iter aux l
  | Custom (_,l) -> List.iter aux l
  | UVar (r,_,_) 
  | AppUVar (r,_,_) when !!r != dummy -> raise NonMetaClosed
  | UVar (r,_,_) -> aux !!r
  | AppUVar (r,_,l) -> aux !!r ; List.iter aux l
  | Arg (i,_) when e.(i) == dummy && not args_safe -> raise NonMetaClosed
  | AppArg (i,_) when e.(i) == dummy -> raise NonMetaClosed
  | Arg (i,_) -> if e.(i) != dummy then aux e.(i)
  | AppArg (i,l) -> aux e.(i) ; List.iter aux l
  | Const _
  | String _
  | Int _
  | Float _ -> ()
 in
  try aux t ; true
  with NonMetaClosed -> false

exception RestrictionFailure

let occurr_check r1 r2 =
  match r1 with
  | None -> ()
  | Some r1 -> if r1 == r2 then raise RestrictionFailure

let empty_env = [||]

let rec make_lambdas destdepth args =
 if args = 0 then let x = UVar(oref dummy,destdepth,0) in x,x
 else let x,y = make_lambdas (destdepth+1) (args-1) in Lam x, y

let mkAppUVar r lvl l =
  try UVar(r,lvl,in_fragment lvl l)
  with NotInTheFragment -> AppUVar(r,lvl,l)

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
       if c >= from then constant_of_dbl (c - delta) else (* locally bound *)
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
    | String _
    | Int _
    | Float _ -> x

    (* fast path with no deref... *)
    | UVar _ when delta == 0 && avoid == None -> x

    (* deref *)
    | UVar ({ contents = t }, vardepth, args) when t != dummy ->
       if depth == 0 then deref_uv ?avoid ~from:vardepth ~to_ args t
       else maux empty_env depth (deref_uv ~from:vardepth ~to_:(from+depth) args t)
    | AppUVar ({ contents = t }, vardepth, args) when t != dummy ->
       if depth == 0 then deref_appuv ?avoid ~from:vardepth ~to_ args t
       else maux empty_env depth (deref_appuv ~from:vardepth ~to_:(from+depth) args t)
    | Arg (i, args) when e.(i) != dummy ->
       deref_uv ?avoid ~from:argsdepth ~to_:(to_+depth) args e.(i)
    | AppArg(i, args) when e.(i) != dummy ->
       let args =
        try smart_map (maux e depth) args
        with RestrictionFailure ->
          anomaly "move: could check if unrestrictable args are unused" in
       deref_appuv ?avoid ~from:argsdepth ~to_:(to_+depth) args e.(i)

    (* heapification/restriction of Arg and AppArg *)
    | Arg (i, args) ->
       if argsdepth < to_ then anomaly "move: invalid Arg heapification";
       let r = oref dummy in
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
       let r = oref dummy in
       let v = UVar(r,to_,0) in
       e.(i) <- v;
       mkAppUVar r to_ args
    | AppArg _ ->
       Fmt.fprintf Fmt.str_formatter
        "Non deterministic pruning, implemented delay: t=%a, delta=%d%!"
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
           let args = mkinterval vardepth argsno 0 in
           let args = List.map (maux empty_env depth) args in
           mkAppUVar r vardepth args
       else
         if vardepth + argsno <= to_ then x
         else begin
           (* TODO/BUG: I believe this assert to be false; if it is, the
              code below is wrong when the assert fails *)
           assert (vardepth+argsno <= from);
           let assignment,fresh = make_lambdas (to_-argsno) argsno in
           if not !last_call then
            trail := (Assign r) :: !trail;
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
         let args0= mkinterval vardepth argsno 0 in
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
           let newvar = UVar(oref dummy,to_,0) in
           if not !last_call then trail := (Assign r) :: !trail;
           r @:= newvar;
           mkAppUVar r vardepth args
       else begin
        Fmt.fprintf Fmt.str_formatter
         "Non deterministic pruning, implemented delay: t=%a, delta=%d%!"
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
  let newr = oref dummy in
  let newargsno = argsno+from-to_ in
  let newvar = UVar(newr,to_,from-to_) in
  if not !last_call then
   trail := (Assign r) :: !trail;
  r @:= newvar;
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
      else constant_of_dbl (c-len) (* NOT LIFTED *)
   | Arg _ | AppArg _ -> anomaly "subst takes a heap term"
   | App(c,x,xs) as orig ->
      let x' = aux depth x in
      let xs' = List.map (aux depth) xs in
      let xxs' = x'::xs' in
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
        | Arg(i,0) -> begin
           try Arg(i,in_fragment fromdepth xxs')
           with NotInTheFragment -> AppArg (i,xxs') end
        | t ->
           let t = hmove ~from:fromdepth ~to_:depth t in
           beta depth [] t xxs'
      else if c < fromdepth then
        if x==x' && xs==xs' then orig else App(c,x',xs')
      else App(c-len,x',xs')
   | Custom(c,xs) as orig ->
      let xs' = List.map (aux depth) xs in
      if xs==xs' then orig else Custom(c,xs')
   | UVar({contents=g},vardepth,argsno) when g != dummy ->
      [%tcall aux depth (deref_uv ~from:vardepth ~to_:depth argsno g)]
   | UVar(r,vardepth,argsno) as orig ->
      if vardepth+argsno <= fromdepth then orig
      else
       let r,vardepth,argsno =
         decrease_depth r ~from:vardepth ~to_:fromdepth argsno in
       let args = mkinterval vardepth argsno 0 in
       let args = List.map (aux depth) args in
       mkAppUVar r vardepth args
   | AppUVar({ contents = t },vardepth,args) when t != dummy ->
      [%tcall aux depth (deref_appuv ~from:vardepth ~to_:depth args t)]
   | AppUVar(r,vardepth,args) ->
      let r,vardepth,argsno =
        decrease_depth r ~from:vardepth ~to_:fromdepth 0 in
      let args0 = mkinterval vardepth argsno 0 in
      let args = List.map (aux depth) (args0@args) in
      mkAppUVar r vardepth args
   | Lam t -> Lam (aux (depth+1) t)
   | String _
   | Int _
   | Float _ as x -> x
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
              let args1 = mkinterval n m 0 in
              AppUVar (r,n,args1@args) end
         | AppUVar (r,depth,args1) -> AppUVar (r,depth,args1@args)
         | Lam _ -> anomaly "beta: some args and some lambdas"
         | String _ | Int _ | Float _ -> type_error "beta"
 end]

(* eat_args n [n ; ... ; n+k] (Lam_0 ... (Lam_k t)...) = n+k+1,[],t
   eat_args n [n ; ... ; n+k]@l (Lam_0 ... (Lam_k t)...) =
     n+k+1,l,t if t != Lam or List.hd l != n+k+1 *)
and eat_args depth l t =
  match t with
  | Lam t' when l > 0 -> eat_args (depth+1) (l-1) t'
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     eat_args depth l (deref_uv ~from:origdepth ~to_:depth args t)
  | AppUVar  ({contents=t},origdepth,args) when t != dummy ->
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
        let args = mkinterval (from+1) (args'-1) 0 in
        App (c,constant_of_dbl from, args)
     | App (c,arg,args2) ->
        let args = mkinterval from args' 0 in
        App (c,arg,args2 @ args)
     | Custom (c,args2) ->
        let args = mkinterval from args' 0 in
        Custom (c,args2 @ args)
     (* TODO: when the UVar/Arg is not dummy, we call deref_uv that
        will call move that will call_deref_uv again. Optimize the
        path *)
     | UVar(t,depth,args2) when from = depth+args2 ->
        UVar(t,depth,args2+args')
     | AppUVar (r,depth,args2) ->
        let args = mkinterval from args' 0 in
        AppUVar (r,depth,args2 @ args)
     | UVar (r,vardepth,argsno) ->
        let args1 = mkinterval vardepth argsno 0 in
        let args2 = mkinterval from args' 0 in
        let args = args1 @ args2 in
        AppUVar (r,vardepth,args)
     | String _
     | Int _
     | Float _ -> t
     | Arg _ | AppArg _ -> assert false (* Uv gets assigned only heap term *)
  end]

;;

let () = Pp.do_deref := deref_uv;;
let () = Pp.do_app_deref := deref_appuv;;

(* }}} *)

 
(* {{{ ************** indexing ********************************** *)

module type Indexing = sig

  type key
  val pp_key : key -> string
  type index
  val key_of : mode:[`Query | `Clause] -> depth:int -> term -> key
  val hd_pred : key clause -> constant
  val add_clauses : key clause list -> (int * term) -> index -> index
  val get_clauses : depth:int -> term -> index -> key clause list
  val make_index : key clause list -> index
  val local_prog : index -> ((*depth:*)int * term) list
end

module TwoMapIndexing : Indexing = struct (* {{{ *)

(* all clauses: used when the query is flexible
   all flexible clauses: used when the query is rigid and the map
                        for that atom is empty
   map: used when the query is rigid before trying the all flexible clauses *)
type key1 = int
type key2 = int
type key = key1 * key2
let hd_pred { key = (hd,_) } = hd

let pp_key (hd,_) = string_of_constant hd

type index = {
  src : (int * term) list;
  map : (key clause list * key clause list * key clause list Elpi_ptmap.t) Elpi_ptmap.t
}

let variablek =    -99999999
let abstractionk = -99999998

let key_of ~mode:_ ~depth =
 let rec skey_of = function
    Const k when k = uvc -> variablek
  | Const k -> k
  | UVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (deref_uv ~from:origdepth ~to_:depth args t)
  | AppUVar ({contents=t},origdepth,args) when t != dummy ->
     skey_of (deref_appuv ~from:origdepth ~to_:depth args t)
  | App (k,_,_) when k = uvc -> variablek
  | App (k,a,_) when k = asc -> skey_of a
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
    key_of_depth (deref_uv ~from:origdepth ~to_:depth args t)
 | AppUVar ({contents=t},origdepth,args) when t != dummy -> 
    key_of_depth (deref_appuv ~from:origdepth ~to_:depth args t)
 | App(k,arg,_) when k == asc -> key_of_depth arg
 | App (k,arg2,_) -> k, skey_of arg2
 | Custom _ -> assert false
 | Arg _ | AppArg _ | Lam _ | UVar _ | AppUVar _ | String _ | Int _ | Float _->
    raise (Failure "Not a predicate")
 in
  key_of_depth

let get_clauses ~depth a { map = m } =
 let ind,app = key_of ~mode:`Query ~depth a in
 try
  let l,flexs,h = Elpi_ptmap.find ind m in
  if app=variablek then l
  else (try Elpi_ptmap.find app h with Not_found -> flexs)
 with Not_found -> []

let add_clauses clauses s { map = p;  src } =       
  let p = List.fold_left (fun m clause ->
    let matching = match clause.mode with [] -> false | x :: _ -> x in
    let ind,app = clause.key in
    try 
      let l,flexs,h = Elpi_ptmap.find ind m in
      if matching then
        if app == variablek then
          Elpi_ptmap.add ind (clause :: l, clause :: flexs, Elpi_ptmap.map (fun l_rev -> clause::l_rev) h) m
        else
          let l_rev = try Elpi_ptmap.find app h with Not_found -> flexs in
          Elpi_ptmap.add ind (l, flexs, Elpi_ptmap.add app (clause::l_rev) h) m
      else
      if app == variablek then
       Elpi_ptmap.add ind
        (clause::l,clause::flexs,Elpi_ptmap.map(fun l_rev->clause::l_rev) h)
        m
      else
       let l_rev = try Elpi_ptmap.find app h with Not_found -> flexs in
        Elpi_ptmap.add ind
         (clause::l,flexs,Elpi_ptmap.add app (clause::l_rev) h) m
    with
    | Not_found when matching ->
     if app == variablek then
      Elpi_ptmap.add ind ([clause],[clause],Elpi_ptmap.empty) m
     else
      Elpi_ptmap.add ind
       ([],[],Elpi_ptmap.add app [clause] Elpi_ptmap.empty) m
    | Not_found -> 
     if app=variablek then
      Elpi_ptmap.add ind ([clause],[clause],Elpi_ptmap.empty) m
     else
      Elpi_ptmap.add ind
       ([clause],[],Elpi_ptmap.add app [clause] Elpi_ptmap.empty) m
    ) p clauses
  in
  { map = p; src = s :: src }

let make_index p =
  let idx = add_clauses (List.rev p) (0,cutc) { map = Elpi_ptmap.empty; src = [] } in
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
    | Const c -> constant_of_dbl (fix_const c)
    | Arg (i,argsno) ->
       (match mkinterval (depth+vars) argsno 0 with
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
    | Lam t -> Lam (aux t)
    | (String _ | Int _ | Float _) as x -> x
  in
  let rec add_pis n t =
   if n = 0 then t else App(pic,Lam (add_pis (n-1) t),[]) in
  add_pis vars (aux t)

let local_prog { src } =  src

end (* }}} *)

module UnifBits : Indexing = struct (* {{{ *)

  type key = int

  type index = {
    src : (int * term) list;
    map : (key clause * int) list Elpi_ptmap.t  (* timestamp *)
  }

  let key_bits =
    let n = ref 0 in
    let m = ref max_int in
    while !m <> 0 do incr n; m := !m lsr 1; done;
    !n

  let hash x = Hashtbl.hash x * 62653
  let fullones = 1 lsl key_bits -1
  let fullzeros = 0
  let abstractionk = 1022   (* TODO *)
  let functor_bits = 6
  let fst_arg_bits = 15
  let max_depth = 1
  let min_slot = 5


  let hd_pred { key } = (- (key land (1 lsl functor_bits - 1)))
  let pp_key hd = string_of_constant (- (hd land (1 lsl functor_bits - 1)))

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

  let key_of ~mode ~depth term =
    let buf = ref 0 in 
    let set_section k left right =
      let k = abs k in
      let new_bits = (k lsl right) land (fullones lsr (key_bits - left)) in
      [%trace "set-section" ("@[<hv 0>%s@ %s@]"
        (dec_to_bin !buf) (dec_to_bin new_bits))
      (buf := new_bits lor !buf) ] in
    let rec index lvl tm depth left right =
      [%trace "index" ("@[<hv 0>%a@]"
        (uppterm depth [] 0 empty_env) tm)
      begin match tm with
      | Const k | Custom (k,_) ->
          set_section (if lvl=0 then k else hash k) left right 
      | UVar ({contents=t},origdepth,args) when t != dummy ->
         index lvl (deref_uv ~from:origdepth ~to_:depth args t) depth left right
      | Lam _ -> set_section abstractionk left right
      | String s -> set_section (hash s) left right
      | Int n -> set_section (hash n) left right
      | Float n -> set_section (hash n) left right
      | Arg _ | UVar _ | AppArg _ | AppUVar _ ->
         if mode = `Clause then set_section fullones left right
         else set_section fullzeros left right
      | App (k,arg,argl) -> 
         let slot = left - right in
         if lvl >= max_depth || slot < min_slot
         then set_section ( if lvl=0 then k else hash k) left right
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
           set_section nk right_hd right;
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
      [%spy "key-val" (fun f x -> Fmt.fprintf f "%s" (dec_to_bin x)) (!buf)];
      !buf

  let get_clauses ~depth a { map = m } =
    let ind = key_of ~mode:`Query ~depth a in
    let cl_list = List.flatten (Elpi_ptmap.find_unifiables ~functor_bits ind m) in
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
    let m = add_clauses ~op:incr p (0,cutc) { map = Elpi_ptmap.empty; src = [] } in
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

(* }}} *)
  
(* open UnifBits *)
open TwoMapIndexing

let ppclause f { args = args; hyps = hyps; key = hd } =
  Fmt.fprintf f "@[<hov 1>%s %a :- %a.@]" (pp_key hd)
     (pplist (uppterm 0 [] 0 empty_env) "") args
     (pplist (uppterm 0 [] 0 empty_env) ",") hyps

(* {{{ ************** unification ******************************* *)

type index = TwoMapIndexing.index
type program = {
  query_depth : int; (* number of sigma/local-introduced variables *)
  idx : index;
  chr : key CHR.t;
  modes : md CMap.t;
}

type goal = (*depth:*)int * index * term

let original_program = Fork.new_local (Obj.magic 0 : index) (* dummy value *)

(* Delayed_goal of (depth, orig_prog, diffed_prog, goal), everything lives in
 * depth (but for orig_prog) *)
(* CAVEAT: we are going to use pointer equality on the contents, so it must
 * be a tuple *)
let print_delayed () =
 List.iter
  (function
   | Delayed_unif (ad,e,bd,a,b),l ->
      Fmt.fprintf Fmt.std_formatter
       "delayed goal: @[<hov 2>^%d:%a@ == ^%d:%a on %a@]\n%!"
        ad (uppterm ad [] 0 empty_env) a
        bd (uppterm ad [] ad e) b
        (pplist (uppterm ad [] 0 empty_env) ",")
        (List.map (fun r -> UVar(r,0,0)) l)
   | Delayed_goal { depth; pdiff; goal = g },l ->
      Fmt.fprintf Fmt.std_formatter
        "delayed goal: @[<hov 2> %a@ ⊢ %a on %a@]\n%!"
          (pplist (fun fmt (depth,t) -> uppterm depth [] 0 empty_env fmt t) ",") pdiff
          (uppterm depth [] 0 empty_env) g
          (pplist (uppterm depth [] 0 empty_env) ",")
          (List.map (fun r -> UVar(r,0,0)) l)
       (* CSC: Bug here: print at the right precedence *)
   ) !delayed
  ;;

print_cstr :=
 (function
   | (Delayed_goal { depth; prog; pdiff; goal }, keys) ->
     Fmt.fprintf Fmt.std_formatter
       (*"Delaying goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
       "Delaying goal: @[<hov 2> ...@ ⊢^%d %a@]\n%!"
         (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*) depth
         (uppterm depth [] 0 empty_env) goal
   | _ -> ())
;;
   

(* is_flex is to be called only on heap terms *)
let rec is_flex =
 function
  | Arg _ | AppArg _ -> anomaly "is_flex called on Args"
  | UVar ({ contents = t }, _, _)
  | AppUVar ({ contents = t }, _, _) when t != dummy -> is_flex t
  | UVar (r, _, _) | AppUVar (r, _, _) -> Some r
  | Const _ | Lam _ | App _ | Custom _ | String _ | Int _ | Float _ -> None

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
    | UVar ({ contents = t }, from, args) when t != dummy ->
        get_con (deref_uv ~from ~to_ args t)
    | AppUVar ({ contents = t }, from, args) when t != dummy -> 
        get_con (deref_appuv ~from ~to_ args t)
    | Arg (i,args) when e.(i) != dummy ->
        get_con (deref_uv ~from:adepth ~to_ args e.(i))
    | AppArg (i,args) when e.(i) != dummy -> 
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
        let c = if hmove then c + delta else c in
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
        (ppterm a [] b e) (constant_of_dbl x) n) "") l
        (ppterm a [] b empty_env) t a delta d w b) begin
    match t with
    | UVar (r1,_,_) | AppUVar (r1,_,_) when r == r1 -> raise RestrictionFailure
    | Const c -> let n = cst c b delta in if n < 0 then constant_of_dbl n else Const n
    | Lam t -> Lam (bind b delta (w+1) t)
    | App (c,t,ts) -> App (cst c b delta, bind b delta w t, List.map (bind b delta w) ts)
    | Custom (c, tl) -> Custom(c, List.map (bind b delta w) tl)
    | String _ | Int _ | Float _ -> t
    (* deref_uv *)
    | Arg (i,args) when e.(i) != dummy ->
        bind a 0 w (deref_uv ~from:a ~to_:(a+d+w) args e.(i))
    | AppArg (i,args) when e.(i) != dummy ->
        bind a 0 w (deref_appuv ~from:a ~to_:(a+d+w) args e.(i))
    | UVar ({ contents = t }, from, args) when t != dummy ->
        bind b delta w (deref_uv ~from ~to_:((if left then b else a)+d+w) args t)
    | AppUVar ({ contents = t }, from, args) when t != dummy ->
        bind b delta w (deref_appuv ~from ~to_:((if left then b else a)+d+w) args t)
    (* pruning *)
    | (UVar _ | AppUVar _ | Arg _ | AppArg _) as _orig_ ->
        (* We deal with all flexible terms in a uniform way *)
        let r, lvl, (is_llam, args), orig_args = match _orig_ with
          | UVar(r,lvl,0) -> r, lvl, (true, []), []
          | UVar(r,lvl,args) ->
              let r' = oref dummy in
              let v = UVar(r',lvl+args,0) in
              r @:= mknLam args v;
              if not !last_call then trail := (Assign r) :: !trail;
              r', (lvl+args),  (true,[]), []
          | AppUVar (r,lvl, orig_args) ->
              r, lvl, is_llam lvl orig_args a b (d+w) left e, orig_args
          | Arg (i,0) ->
              let r = oref dummy in
              let v = UVar(r,a,0) in
              e.(i) <- v;
              r, a, (true,[]), []
          | Arg (i,args) ->
              let r = oref dummy in
              let v = UVar(r,a,0) in
              e.(i) <- v;
              let r' = oref dummy in
              let v' = UVar(r',a+args,0) in
              r @:= mknLam args v';
              r', a+args, (true, []), []
          | AppArg (i,orig_args) ->
              let is_llam, args = is_llam a orig_args a b (d+w) false e in
              let r = oref dummy in
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
                      (constant_of_dbl i, constant_of_dbl (cst ~hmove:false i b delta))
                        :: keep_cst_for_lvl rest in
              List.split (keep_cst_for_lvl (List.sort Pervasives.compare l)) in
            let r' = oref dummy in
            r @:= mknLam n_args (mkAppUVar r' gamma args_gamma_lvl_abs);
            if not !last_call then trail := (Assign r) :: !trail;
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
                  constant_of_dbl (c_p + lvl) :: a_lvl,
                  constant_of_dbl i :: a_here
                with RestrictionFailure -> acc) args ([],[]) in
            if n_args = List.length args_here then
              (* no pruning, just binding the args as a normal App *)
              mkAppUVar r lvl (List.map (bind b delta w) orig_args)
            else
              (* we need to project away some of the args *)
              let r' = oref dummy in
              let v = mkAppUVar r' lvl args_lvl in
              r @:= mknLam n_args v;
              if not !last_call then trail := (Assign r) :: !trail;
              (* This should be the beta reduct. One could also
               * return the non reduced but bound as in the other if branch *)
              mkAppUVar r' lvl args_here
        end
          else raise RestrictionFailure
  end] in
  try
    r @:= mknLam new_lams (bind b delta 0 t);
    if not !last_call then trail := (Assign r) :: !trail;
    [%spy "assign(HO)" (ppterm gamma [] a empty_env) (!!r)];
    true
  with RestrictionFailure -> false
;;
exception Non_linear

let rec list_to_lp_list = function
  | [] -> nilc
  | x::xs -> App(consc,x,[list_to_lp_list xs])
;;
 let rec unif matching depth adepth a bdepth b e =
   [%trace "unif" ("@[<hov 2>^%d:%a@ =%d%s= ^%d:%a@]%!"
       adepth (ppterm (adepth+depth) [] adepth empty_env) a
       depth (if matching then "m" else "")
       bdepth (ppterm (bdepth+depth) [] adepth e) b)
   begin let delta = adepth - bdepth in
   (delta = 0 && a == b) || match a,b with
  
   (* _ as X binding *)
   | _, App(c,arg,[(Arg _ | AppArg _) as as_this]) when c == asc ->
      unif matching depth adepth a bdepth arg e &&
      unif matching depth adepth a bdepth as_this e 
   | _, App(c,arg,_) when c == asc -> error "syntax error in as"
   | App(c,arg,_), _ when c == asc ->
      unif matching depth adepth arg bdepth b e

(* TODO: test if it is better to deref_uv first or not, i.e. the relative order
   of the clauses below *)
   | UVar(r1,_,args1), UVar(r2,_,args2) when r1 == r2 -> args1 == args2

   (* deref_uv *)
   | UVar ({ contents = t }, from, args), _ when t != dummy ->
      unif matching depth adepth (deref_uv ~from ~to_:(adepth+depth) args t) bdepth b e
   | AppUVar ({ contents = t }, from, args), _ when t != dummy -> 
      unif matching depth adepth (deref_appuv ~from ~to_:(adepth+depth) args t) bdepth b e
   | _, UVar ({ contents = t }, from, args) when t != dummy ->
      unif matching depth adepth a bdepth (deref_uv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, AppUVar ({ contents = t }, from, args) when t != dummy ->
      unif matching depth adepth a bdepth (deref_appuv ~from ~to_:(bdepth+depth) args t) empty_env
   | _, Arg (i,args) when e.(i) != dummy ->
(*        if matching then raise Non_linear; *)
      (* XXX BROKEN deref_uv invariant XXX
       *   args not living in to_ but in bdepth+depth *)
      unif matching depth adepth a adepth
        (deref_uv ~from:adepth ~to_:(adepth+depth) args e.(i)) empty_env
   | _, AppArg (i,args) when e.(i) != dummy -> 
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
   | (UVar _ | AppUVar _), Const c when c == uvc && matching -> true
   | (UVar(r,vd,_) | AppUVar(r,vd,_)), App(c,hd,[]) when c == uvc && matching ->
      unif matching depth adepth (UVar(r,vd,0)) bdepth hd e
   | UVar(r,vd,ano), App(c,hd,[arg]) when c == uvc && matching ->
      let basedepth = 0 in (* XXX BUG? WE CAN DO BETTER *)
      let r,implargs =
       if vd <= basedepth then r,0
       else begin
        let r' = oref dummy in
        let implargs = vd - basedepth in
        let newvar = UVar(r',basedepth,implargs) in
        if not !last_call then trail := (Assign r) :: !trail;
        r @:= newvar;
        [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
        r', implargs
       end in
      unif matching depth adepth (UVar(r,0,0)) bdepth hd e &&
      let args = list_to_lp_list (mkinterval basedepth (implargs + ano) 0) in
      unif matching depth adepth args bdepth arg e
   | AppUVar(r,vd,args), App(c,hd,[arg]) when c == uvc && matching ->
      (* CODE CUT&PASTE FROM CASE ABOVE *)
      let basedepth = 0 in (* XXX BUG? WE CAN DO BETTER *)
      let r,implargs =
       if vd <= basedepth then r,0
       else begin
        let r' = oref dummy in
        let implargs = vd - basedepth in
        let newvar = UVar(r',basedepth,implargs) in
        if not !last_call then trail := (Assign r) :: !trail;
        r @:= newvar;
        [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
        r', implargs
       end in
      let args = mkinterval basedepth implargs 0 @ args in
      unif matching depth adepth (UVar(r,vd,0)) bdepth hd e &&
      let args = list_to_lp_list args in
      unif matching depth adepth args bdepth arg e
   | _, (Const c | App(c,_,_)) when c == uvc -> false
   (*
      error (string_of_constant uvc ^ " can be used only in matching and takes 0, 1 or 2 args " ^ show_term a)

*)
   (* assign *)
   | _, Arg (i,0) ->
     begin try
      e.(i) <- hmove ~from:(adepth+depth) ~to_:adepth a;
      [%spy "assign" (ppterm adepth [] adepth empty_env) (e.(i))]; true
     with RestrictionFailure -> false end
   | _, UVar (r,origdepth,0) ->
       if not !last_call then
        trail := (Assign r) :: !trail;
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
       if not !last_call then
        trail := (Assign r) :: !trail;
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
   | _, UVar (r,origdepth,args) (*when not matching*) when args>0 ->
      if not !last_call then
       trail := (Assign r) :: !trail;
      r @:= fst (make_lambdas origdepth args);
      [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
      unif matching depth adepth a bdepth b e
   | UVar (r,origdepth,args), _ (*when not matching*) when args >0 ->
      if not !last_call then
       trail := (Assign r) :: !trail;
      r @:= fst (make_lambdas origdepth args);
      [%spy "assign" (ppterm depth [] adepth empty_env) (!!r)];
      unif matching depth adepth a bdepth b e

   (* HO *)
   | other, AppArg(i,args) ->
       let is_llam, args = is_llam adepth args adepth bdepth depth false e in
       if is_llam then
         let r = oref dummy in
         e.(i) <- UVar(r,adepth,0);
         bind r adepth args adepth depth delta bdepth false other e
       else begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth e) b ;
       let r = oref dummy in
       e.(i) <- UVar(r,adepth,0);
       let delayed_goal = Delayed_unif (adepth+depth,e,bdepth+depth,a,b) in
       let (_,vars) as delayed_goal =
        match is_flex other with
           None -> delayed_goal, [r]
         | Some r' -> delayed_goal, if r==r' then [r] else [r;r'] in
       delayed := delayed_goal :: !delayed;
       List.iter (fun r -> r.rest <- delayed_goal :: r.rest) vars ;
       if not !last_call then trail := AddConstr delayed_goal :: !trail;
       true
       end
   | AppUVar (r, lvl,args), other when not matching ->
       let is_llam, args = is_llam lvl args adepth bdepth depth true e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth true other e
       else begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth empty_env) b ;
       let delayed_goal = Delayed_unif (adepth+depth,e,bdepth+depth,a,b) in
       let (_,vars) as delayed_goal =
        match is_flex other with
           None -> delayed_goal, [r]
         | Some r' -> delayed_goal, [r;r'] in
       List.iter (fun r -> r.rest <- delayed_goal :: r.rest) vars ;
       delayed := delayed_goal :: !delayed;
       true
       end
   | other, AppUVar (r, lvl,args) when not matching ->
       let is_llam, args = is_llam lvl args adepth bdepth depth false e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth false other e
       else begin
       Fmt.fprintf Fmt.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth empty_env) a (uppterm depth [] bdepth e) b ;
       let delayed_goal = Delayed_unif (adepth+depth,e,bdepth+depth,a,b) in
       let delayed_goal =
        match is_flex other with
           None -> delayed_goal, [r]
         | Some r' -> delayed_goal, if r==r' then [r] else [r;r'] in
       add_constraint delayed_goal ;
       true
       end
  
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
   | Int s1, Int s2 -> s1==s2
   | Float s1, Float s2 -> s1 = s2
   | String s1, String s2 -> s1==s2
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
(* {{{ ************** backtracking ****************************** *)


let undo_trail old_trail =
(* Invariant: to_resume and new_delayed are always empty when a choice
   point is created. This invariant is likely to break in the future,
   when we allow more interesting constraints and constraint propagation
   rules. *)
  to_resume := []; new_delayed := [];
  while !trail != old_trail do
    match !trail with
    | Assign r :: rest -> r.contents <- dummy; trail := rest
    | AddConstr exn :: rest -> remove_constraint0 exn ; trail := rest
    | DelConstr exn :: rest -> add_constraint0 exn ; trail := rest
    | [] -> anomaly "undo to unknown trail"
  done
;;

(* The activation frames points to the choice point that
   cut should backtrack to, i.e. the first one not to be
   removed. For bad reasons, we call it lvl in the code. *)
type frame =
 | FNil
(* TODO: to save memory, introduce a list of triples *)
 | FCons of (*lvl:*)alternative * goal list * frame
and alternative = {
  lvl : alternative;
  program : index;
  depth : int;
  goal : term;
  goals : goal list;
  stack : frame;
  trail : trail_item list;
  clauses : key clause list;
  next : alternative
}
let emptyalts : alternative = Obj.magic 0

(* }}} *)

let rec split_conj = function
  | App(c, hd, args) when c == andc || c == andc2 ->
      split_conj hd @ List.(flatten (map split_conj args))
  | f when f == truec -> []
  | _ as f -> [ f ]
;;

let rec lp_list_to_list = function
  | App(c, hd, [tl]) when c == consc -> hd :: lp_list_to_list tl
  | f when f == nilc -> []
  | x -> error (Fmt.sprintf "%s is not a list" (show_term x))
;;

let rec get_lambda_body depth = function
 | UVar ({ contents=g },from,args) when g != dummy ->
    get_lambda_body depth (deref_uv ~from ~to_:depth args g)
 | AppUVar ({contents=g},from,args) when g != dummy -> 
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

let rec term_map m = function
  | Const x when List.mem_assoc x m -> constant_of_dbl (List.assoc x m)
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
  | (Int _ | String _ | Float _) as x -> x

let clausify vars depth t =
  let rec claux vars depth hyps ts lts lcs t =
  [%trace "clausify" ("%a %d %d %d %d\n%!"
      (ppterm (depth+lts) [] 0 empty_env) t depth lts lcs (List.length ts)) begin
  match t with
  | App(c, g, gs) when c == andc || c == andc2 ->
     let res = claux vars depth hyps ts lts lcs g in
     List.fold_right
      (fun g (clauses,lts) ->
        let moreclauses,lts = claux vars depth hyps ts lts lcs g in
         clauses@moreclauses,lts
      ) gs res
  | App(c, g2, [g1]) when c == rimplc ->
     claux vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == rimplc -> assert false
  | App(c, g1, [g2]) when c == implc ->
     claux vars depth ((ts,g1)::hyps) ts lts lcs g2
  | App(c, _, _) when c == implc -> assert false
  | App(c, arg, []) when c == sigmac ->
     let b = get_lambda_body (depth+lts) arg in
     let args =
      List.rev (List.filter (function (Arg _) -> true | _ -> false) ts) in
     let cst =
      match args with
         [] -> Const (depth+lcs)
       | hd::rest -> App (depth+lcs,hd,rest) in
     claux vars depth hyps (cst::ts) (lts+1) (lcs+1) b
  | App(c, arg, []) when c == pic ->
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
       | Lam _ | Custom _ | String _ | Int _ | Float _ -> assert false
       | UVar _ | AppUVar _ -> assert false
     in
     let all_modes =
      let mode =
        try CMap.find hd !modes
        with Not_found -> Multi [] in
      match mode with
      | Mono [] -> assert false
      | Mono m -> [g,args,hyps,m]
      | Multi l ->
           (g,args,hyps,[]) ::
           List.map (fun (k,subst) ->
             let map = term_map ((hd,k) :: subst) in
             match CMap.find k !modes with
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
  | UVar ({ contents=g },from,args) when g != dummy ->
     claux vars depth hyps ts lts lcs
       (deref_uv ~from ~to_:(depth+lts) args g)
  | AppUVar ({contents=g},from,args) when g != dummy -> 
     claux vars depth hyps ts lts lcs
       (deref_appuv ~from ~to_:(depth+lts) args g)
  | Arg _ | AppArg _ -> anomaly "claux called on non-heap term"
  | Lam _ | Custom _ | String _ | Int _ | Float _ ->
     error "Assuming a custom or string or int or float or function"
  | UVar _ | AppUVar _ -> error "Flexible assumption"
  end] in
    claux vars depth [] [] 0 0 t
;;

(* {{{ ************** run *************************************** *)

exception No_clause

let register_custom, lookup_custom =
 let (customs :
      (* Must either raise No_clause or succeed with the list of new goals *)
      ('a, depth:int -> env:term array -> index -> term list -> term list)
      Hashtbl.t)
   =
     Hashtbl.create 17 in
 let check s = 
    if s = "" || s.[0] <> '$' then
      anomaly ("Custom predicate name " ^ s ^ " must begin with $");
    let idx = fst (funct_of_ast (F.from_string s)) in
    if Hashtbl.mem customs idx then
      anomaly ("Duplicate custom predicate name " ^ s);
    idx in
 (fun s f ->
    let idx = check s in
    Hashtbl.add customs idx f),
 Hashtbl.find customs
;;

let do_make_runtime : (unit -> (?pr_delay:bool -> ?depth:int -> 'a -> 'b -> 'c -> md CMap.t -> int -> 'k) * 'e * 'f) ref =
 ref (function () -> anomaly "do_make_runtime not initialized")

exception NoMatch

let rec list_assq1 p = function
  | [] -> raise Not_found
  | ((r,_), data) :: _ when r == p -> data
  | _ :: rest -> list_assq1 p rest
;;

let rec freeze ad m = function
  | UVar( { contents = t} , 0,0) when t != dummy -> freeze ad m t
  | UVar( { contents = t} , vardepth, args) when t != dummy -> assert false
(*      freeze ad m (deref_uv ~from:vardepth ~to_:ad args t)*)
    
  | AppUVar ( { contents = t }, _, _) when t != dummy -> assert false
  | UVar( r, lvl, ano) ->
     let m, (c, n) =
      (try m, list_assq1 r m
       with Not_found ->
         let n, x = new_fresh_constant () in
         [%spy "freeze ad" (fun fmt tt -> Fmt.fprintf fmt "%s == %a" (string_of_constant n) (ppterm 0 [] 0 empty_env) tt) (UVar (r,lvl,0))];
         ((r,lvl),(x,n)) :: m, (x,n)) in
     m, (match mkinterval 0 (lvl+ano) 0 with
        | [] -> c
        | [x] -> App(n,x,[])
        | x::xs -> App(n,x,xs))
  | AppUVar( r, lvl, args ) ->
     let m, (c, n) =
      (try m, list_assq1 r m
       with Not_found ->
         let n, x = new_fresh_constant () in
         [%spy "freeze ad" (fun fmt tt -> Fmt.fprintf fmt "%s == %a" (string_of_constant n) (ppterm 0 [] 0 empty_env) tt) (UVar (r,lvl,0))];
         ((r,lvl),(x,n)) :: m, (x,n)) in
     let m, args = List.fold_right (fun x (m,l) ->
        let m, x = freeze ad m x in
        (m, x ::l)) args (m,[]) in
     m, (match mkinterval 0 lvl 0 @ args with
        | [] -> c
        | [x] -> App(n,x,[])
        | x::xs -> App(n,x,xs))
  | App(c,x,xs) ->
      let m, x = freeze ad m x in
      let m, xs = List.fold_right (fun x (m,l) ->
        let m, x = freeze ad m x in
        (m, x ::l)) xs (m,[]) in
      m, App(c,x,xs)
  | Const _ as x -> m, x
  | Arg _ | AppArg _ -> anomaly "freeze ad: not an heap term"
  | Lam t -> let m, t = freeze (ad+1) m t in m, Lam t
  | (Int _ | Float _ | String _) as x -> m, x
  | Custom(c,xs) ->
      let m, xs = List.fold_right (fun x (m,l) ->
        let m, x = freeze ad m x in
        (m, x ::l)) xs (m,[]) in
      m, Custom(c,xs)
;;
let freeze ad m t =
  [%spy "freeze-in"  (ppterm 0 [] 0 empty_env) t];
  let m, t' = freeze ad  m t in
  [%spy "freeze-out"  (ppterm 0 [] 0 empty_env) t'];
  m, t'


let rec list_assq2 p = function
  | [] -> raise Not_found
  | (data, (_,k)) :: _ when k == p -> data
  | _ :: rest -> list_assq2 p rest
;;
let rec list_assq21 p = function
  | [] -> raise Not_found
  | (_, (data,k)) :: _ when k == p -> data
  | _ :: rest -> list_assq21 p rest
;;

let is_frozen c m =
   try
     let _r = list_assq2 c m in true
   with Not_found -> false
;;

let matching e depth argsdepth m a b =
  if unif ~matching:true argsdepth e depth a b
  then
    fst(Array.fold_left (fun (m,i) ei ->
      if ei != dummy then
        let m, ei = freeze argsdepth m ei in
        e.(i) <- ei;
        m,i+1
      else
        m,i+1
      ) (m,0) e)
  else raise NoMatch
(*
  let rec aux m a b =
  [%trace "matching" ("%a = %a" (ppterm 0 [] 0 e) a (ppterm 0 [] 0 e) b)
  begin match a,b with
  | UVar( { contents = t}, 0, 0), _ when t != dummy -> aux m t b
  | _, Arg(i,0) when e.(i) != dummy -> aux m a e.(i)
  | t, Arg(i,0) -> let m, t = freeze m t in e.(i) <- t; m 
  | t, App(c,Arg(i,0),[Arg(j,0)]) when c == destappc ->
      let m, t = freeze m t in
      (match t with
      | Const f when is_frozen f m -> e.(i) <- a; e.(j) <- nilc; m
      | App(f,x,xs) when is_frozen f m->
         e.(i) <- list_assq21 f m; e.(j) <- list_to_lp_list (x::xs); m
      | _ -> raise NoMatch)
  | UVar( r,0,0), (Const _ as d) ->
      (try
        let c = fst (list_assq1 r m) in
        if c == d then m else raise NoMatch
      with Not_found -> raise NoMatch)
  | App(c1,x,xs), App(c2,y,ys) when c1 == c2 ->
      let m = aux m x y in
      let m = List.fold_left2 aux m xs ys in
      m
  | Const c1, Const c2 ->
      if c1 >= depth && c2 >= depth then if a == b then m else raise NoMatch
      else
        if a == b then m (* FIXME in the HO case *)
        else
          raise NoMatch
  | _, AppArg _ -> assert false
  | Lam a, Lam b -> aux m a b
  | Int x, Int y when x == y -> m
  | Float x, Float y when x = y -> m
  | String x, String y when x == y -> m
  | _ -> raise NoMatch
  end] in
    aux m a b
*)
;;

let thaw max_depth e m t =
  let rec aux = function
  | UVar( { contents = t} , lvl, ano) when t != dummy ->
      aux (deref_uv ~from:lvl ~to_:max_depth ano t)
  | AppUVar( { contents = t} , lvl, args) when t != dummy ->
      aux (deref_appuv ~from:lvl ~to_:max_depth args t)
  | Arg(i, ano) when e.(i) != dummy ->
      aux (deref_uv ~from:max_depth ~to_:max_depth ano e.(i))
  | AppArg(i, args) when e.(i) != dummy ->
      aux (deref_appuv ~from:max_depth ~to_:max_depth args e.(i))
  | Arg(i,ano) -> e.(i) <- UVar(oref dummy,max_depth,ano); e.(i)
  | AppArg(i,args) ->
      e.(i) <- mkAppUVar (oref dummy) max_depth (List.map aux args); e.(i)
  | App(c,x,xs) ->
      (try
        let r, lvl = list_assq2 c m in
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
        let r, lvl = list_assq2 x m in
        if lvl = 0 then
         UVar(r,lvl,0)
        else
         let r' = oref dummy in
         (*if not !last_call then
          trail := (Assign r) :: !trail; ????? *)
         r @:= UVar(r',0,lvl);
         UVar (r', 0, 0)
      with Not_found -> orig)
  | (Int _ | Float _ | String _) as x -> x
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

module HISTORY = Hashtbl.Make(struct
  type t = key clause * constraint_ list
  let hash = Hashtbl.hash
  let equal (p,lp) (p',lp') = p == p' && for_all2 (==) lp lp'
end)

(* hmove a term possibly containing Args *)
(* TODO: the function is almost identical to the aux of close_with_pis
   but here we do not instantiate Args. The two codes must be unified *)
let lift_pat ~from ~to_ t =
  let delta = to_ - from in
  let rec aux = function
  | Const n as x ->
     if n < from then x else constant_of_dbl (n + delta)
  | Lam r -> Lam (aux r)
  | App (n,x,xs) ->
      App((if n < from then n else n + delta), aux x, List.map aux xs)
  | Arg _ as x -> x
  | AppArg(i,xs) -> AppArg(i,List.map aux xs)
  | UVar _ as x ->
     (* TODO: quick hack here, but it does not work for AppUVar *)
     hmove ~from ~to_ x
  | AppUVar _ -> assert false
  | Custom(c,xs) -> Custom(c,List.map aux xs)
  | (String _ | Int _ | Float _) as x -> x
  in
    aux t
;;

let chrules = Fork.new_local CHR.empty

let delay_goal ?(filter_ctx=fun _ -> true) ~depth prog ~goal:g ~on:keys =
  let pdiff = local_prog prog in
  let pdiff = List.filter filter_ctx pdiff in
(*
  [%spy "delay-goal" (fun fmt (depth,x)-> Fmt.fprintf fmt
    (*"Delaying goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
    "@[<hov 2> ...@ ⊢^%d %a@]\n%!"
      (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*) depth
      (uppterm depth [] 0 empty_env) x) g];
*)
  let delayed_goal = (Delayed_goal { depth; prog = Obj.magic prog; pdiff; goal = g }, keys) in
  add_constraint delayed_goal
;;

let rec head_of = function
  | Const x -> x
  | App(x,_,_) -> x
  | AppUVar(r,_,_)
  | UVar(r,_,_) when !!r != dummy -> head_of !!r
  | _ -> anomaly "strange head"

let declare_constraint ~depth prog ~goal:g ~on:keys =
  let clique = CHR.clique_of (head_of g) !chrules in 
  (* XXX head_of is weak because no clausify ??? XXX *)
  delay_goal ~filter_ctx:(fun (_,x) -> CSet.mem (head_of x) clique)
    ~depth prog ~goal:g ~on:keys
let delay_goal ~depth prog ~goal:g ~on:keys =
  delay_goal ~depth prog ~goal:g ~on:keys


(* constr is a new_delayed constraint;
   the two lists in output are the constraints to be removed and added *)
let propagate constr j history =
 let sequent_of_constr constr =
  match constr with
     Delayed_unif _,_ ->
      anomaly "Delayed unifications should not become new_delayed"
   | Delayed_goal { depth; pdiff = p; goal = t },_ -> depth,p,t in
 let rec find_entails nargs_ref max_depth n = function
   | Lam t -> find_entails nargs_ref max_depth (n+1) t
   | App(c,x,[g]) when c == entailsc -> n, x, g
   | t ->
      let i = !nargs_ref in
      incr nargs_ref; 
      n, Arg(i,0), t in
 let sequent_of_pattern nargs_ref max_depth ruledepth = function
   | App(c,x,[]) when c == nablac ->
       let min_depth, ctx, g = find_entails nargs_ref max_depth ruledepth x in
       (min_depth, ctx, g)
   | Lam _ -> error "syntax error in propagate"
   | x -> 
       let min_depth, ctx, g = find_entails nargs_ref max_depth ruledepth x in
       (min_depth, ctx, g) in
 (*Fmt.fprintf Fmt.std_formatter "PROPAGATION %d\n%!" j;*)
 (* CSC: INVARIANT: propagate clauses can never be assumed using
    implication. Otherwise ~depth:0 is wrong and I do not see any
    reasonable semantics (i.e. a semantics where the scoping is not
    violated). For the same reason I took the propagate clauses from
    the !original_program. *)
 let rules =
   let _,_,t = sequent_of_constr constr in
   let hd = head_of t in
   CHR.rules_for hd !chrules in

 let p = !original_program in

 let run,_,no_delayed = !do_make_runtime () in
 let no_such_j = ref true in
 let result =
    map_exists (function ({ depth = ruledepth; args = [ g1; g2; g3];
                     hyps = hyps; vars = nargs; key = k } as clause) ->

    let gg1 = lp_list_to_list g1 in
    let gg2 = lp_list_to_list g2 in
    let leng1 = List.length gg1 in

    let headsno = leng1 + List.length gg2 in
    if headsno < 1 then error "no heads in propagate" ;
 [%spy "propagate-j" (fun fmt -> Format.fprintf fmt "%d") j];
 [%spy "propagate-headsno" (fun fmt -> Format.fprintf fmt "%d") headsno];
 [%spy "propagate-constr" (fun fmt -> Format.fprintf fmt "%a" (uppterm 0 [] 0 empty_env)) ((fun (_,_,t) -> t) (sequent_of_constr constr))];
 [%spy "propagate-delayed" (fun fmt -> Format.fprintf fmt "%a" (pplist (uppterm 0 [] 0 empty_env) ";")) (List.map (fun (_,_,t) -> t) (List.map sequent_of_constr !delayed))];
    if j >= headsno then None
    else
    let combinations =
     let rec insert x =
      function
         [] -> [[x]]
       | (hd::tl) as l -> (x::l) :: (List.map (fun y -> hd::y) (insert x tl)) in
     let rec aux n l : 'a list list =
       if n = 0 then [[]] else
       match l with 
          [] -> []
        | hd::tl when hd == constr-> aux n tl
        | hd::tl-> List.flatten (List.map (insert hd) (aux (n-1) tl)) @ aux n tl
     in
      aux (headsno - 1) !delayed in

     [%spy "propagate-combs" (fun fmt -> Fmt.fprintf fmt "%d") (List.length combinations)];
     
    let combinations =
      combinations |> List.map (fun l ->
        let before, after = partition_i (fun i _ -> i < j) l in
        before @ constr :: after
        ) in

     combinations |> map_exists (fun heads ->
      let hitem = clause,heads in
      no_such_j := false;
      if HISTORY.mem history hitem then begin
(*         Fmt.fprintf Fmt.std_formatter "pruned\n%!" ; *)
        None
        end
      else
       let () = HISTORY.add history hitem () in
       let heads_sequent = List.map sequent_of_constr heads in
       let max_depth =
         List.fold_left (fun acc (d,_,_) -> max d acc) ruledepth heads_sequent in
       let contexts, goals_at_max_depth =
         List.fold_right (fun (d,p,g) (ctxs, gs) ->
           p :: ctxs, hmove ~from:d ~to_:max_depth g :: gs)
           heads_sequent ([],[]) in

       let to_match, to_remove =
         partition_i (fun i _ -> i < leng1) goals_at_max_depth in
       let _, heads_to_remove =
         partition_i (fun i _ -> i < leng1) heads in

       let lift_pattern_sequent (d,ctx,g) =
         if d > max_depth then raise NoMatch;
         d, ctx, lift_pat ~from:d ~to_:max_depth g in

       try
         let nargs = ref nargs in
         let sequent_of_pattern = sequent_of_pattern nargs max_depth ruledepth in
         let patterns_sequent1 =
           List.(gg1 |> map sequent_of_pattern |> map lift_pattern_sequent) in
         let patterns_sequent2 =
           List.(gg2 |> map sequent_of_pattern |> map lift_pattern_sequent) in

         let e = Array.make !nargs dummy in
         (*Fmt.fprintf Fmt.std_formatter "attempt: %a = %a\n%!"
           (pplist (uppterm max_depth [] 0 empty_env) ",") (to_match @ to_remove)
           (pplist (fun fmt (_,_,g) ->
              uppterm max_depth [] 0 e fmt g) ",")
           (patterns_sequent1 @ patterns_sequent2);*)
         let match_p m t (d,_,pat) = matching e max_depth (max_depth(*-d*)) m t pat in
         let m = List.fold_left2 match_p [] to_match  patterns_sequent1 in
         let m = List.fold_left2 match_p m  to_remove patterns_sequent2 in
         (* check all aligned max_depth *)
         let contexts_at_max_depth = contexts |>
           List.map (fun p -> List.map (fun (d,t) -> hmove ~from:d ~to_:max_depth t) p) in
         let ctxs_to_match, ctxs_to_remove =
           partition_i (fun i _ -> i < leng1) contexts_at_max_depth in

         let match_ctx m lt (d,ctx,_) =
           let t = list_to_lp_list lt in
           matching e max_depth (max_depth-d) m t ctx in
         let m = List.fold_left2 match_ctx m ctxs_to_match  patterns_sequent1 in
         let m = List.fold_left2 match_ctx m ctxs_to_remove patterns_sequent2 in

         let gg3 = lift_pat ~from:0 ~to_:max_depth g3 in

         let pp_action success ng =
           if success then
           let pp_seq fmt (a,b) =
             if a = [] then uppterm 0 [] 0 empty_env fmt b
             else
              Fmt.fprintf fmt "%a ?- %a"
               (pplist (uppterm 0 [] 0 empty_env) "; ") a
               (uppterm 0 [] 0 empty_env) b in
           Fmt.eprintf
             "CHR: @[<v>@[<hov 2>%a@ :- %a@]@ on   [%a] [%a]@ %s %a@]\n%!"
              (uppterm 0 [] 0 empty_env) (App(rulec,g1,[g2;g3]))
              (pplist (uppterm 0 [] 0 empty_env) ", ") hyps
              (pplist pp_seq " ") (List.combine ctxs_to_match to_match)
              (pplist pp_seq " ") (List.combine ctxs_to_remove to_remove)
              (if success then "new " else "guard fails")
              (uppterm 0 [] 0 e) ng
         in

         match hyps with
         | [] ->
             let ng = thaw max_depth e m gg3 in
             pp_action true ng;
             Some(heads_to_remove,[ { depth = max_depth; prog = Obj.magic p; pdiff = []; goal = ng}])
         | h1 :: hs ->
            let query = [],max_depth,e,App(andc,h1,hs) in
            (try
              (* CSC: I am not at all sure about the second occurrence of
                 max_depth below *)
              let _ = run ~depth:max_depth p query CHR.empty CMap.empty max_depth in
              if not (no_delayed ()) then begin
                anomaly "propagation rules must not $delay"
              end;
              let ng = thaw max_depth e m gg3 in
              pp_action true ng;
              Some(heads_to_remove,[ { depth = max_depth; prog = Obj.magic p; pdiff = []; goal = ng }])
            with No_clause ->
              pp_action false cutc;
              None)
       with NoMatch -> (*Fmt.fprintf Fmt.std_formatter "NoMatch\n%!";*)None)
     | _ -> anomaly "propagate expects 3 args") rules
 in
 match result with
 | Some x -> `Matched x
 | None when !no_such_j -> `NoSuchJ
 | _ -> `NoMatch
;;

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : unit -> (?pr_delay:bool -> ?depth:int -> 'a -> 'b -> 'c -> md CMap.t -> int -> 'k) * (?pr_delay:bool -> 'k -> 'k) * (unit -> bool) =

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
    run ndepth np ng (goals@(depth,p,g)::gs) next alts lvl
 | Some [] ->
    match g with
    | c when c == cutc -> [%tcall cut p gs next alts lvl]
    | App(c, g, gs') when c == andc || c == andc2 ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    | App(c, g2, [g1]) when c == rimplc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, lcs = clausify 0 depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses clauses (depth,g1) p) g2 gs next alts lvl
    | App(c, g1, [g2]) when c == implc ->
       (*Fmt.eprintf "RUN: %a\n%!" (uppterm depth [] 0 empty_env) g ;*)
       let clauses, lcs = clausify 0 depth g1 in
       let g2 = hmove ~from:depth ~to_:(depth+lcs) g2 in
       (*Fmt.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 empty_env) g2;*)
       run (depth+lcs) (add_clauses clauses (depth,g1) p) g2 gs next alts lvl
(*  This stays commented out because it slows down rev18 in a visible way!   *)
(*  | App(c, _, _) when c == implc -> anomaly "Implication must have 2 args" *)
    | App(c, arg, []) when c == pic ->
       let f = get_lambda_body depth arg in
       run (depth+1) p f gs next alts lvl
    | App(c, arg, []) when c == sigmac ->
       let f = get_lambda_body depth arg in
       let v = UVar(oref dummy, depth, 0) in
       run depth p (subst depth [v] f) gs next alts lvl
    | UVar ({ contents = g }, from, args) when g != dummy ->
       run depth p (deref_uv ~from ~to_:depth args g) gs next alts lvl
    | AppUVar ({contents = t}, from, args) when t != dummy ->
       run depth p (deref_appuv ~from ~to_:depth args t) gs next alts lvl 
    | Const _ | App _ -> (* Atom case *)
       let cp = get_clauses depth g p in
       [%tcall backchain depth p g gs cp next alts lvl]
    | Arg _ | AppArg _ -> anomaly "Not a heap term"
    | Lam _ | String _ | Int _ | Float _ -> type_error "Not a predicate"
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
    let maybe_last_call = alts == emptyalts in
    let rec args_of = function
      | Const k -> k, []
      | App(k,x,xs) -> k, x::xs
      | UVar ({ contents = g },origdepth,args) when g != dummy ->
         args_of (deref_uv ~from:origdepth ~to_:depth args g) 
      | AppUVar({ contents = g },origdepth,args) when g != dummy ->
         args_of (deref_appuv ~from:origdepth ~to_:depth args g) 
      | _ -> anomaly "ill-formed goal" in
    let k, args_of_g = args_of g in
    let rec select l =
      [%trace "select" (fun fmt -> pplist ~max:1 ~boxed:true ppclause "|" fmt l)
      begin match l with
      | [] -> [%tcall next_alt alts]
      | c :: cs ->
        let old_trail = !trail in
        last_call := maybe_last_call && cs = [];
        let env = Array.make c.vars dummy in
        match
         for_all3b (fun x y b -> unif ~matching:b depth env c.depth x y)
           args_of_g c.args c.mode false
        with
        | false -> undo_trail old_trail; [%tcall select cs]
        | true ->
           let oldalts = alts in
           let alts = if cs = [] then alts else
             { program = p; depth = depth; goal = g; goals = gs; stack = next;
               trail = old_trail; clauses = cs; lvl = lvl ; next = alts} in
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
    if alts == emptyalts then trail := [];
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
   while !ok && !to_resume <> [] do
     match !to_resume with
     | (Delayed_unif (ad,e,bd,a,b), vars) as exn :: rest ->
         remove_constraint exn;
         to_resume := rest;
         (*Fmt.fprintf Fmt.std_formatter
          "Resuming @[<hov 2>^%d:%a@ == ^%d:%a@]\n%!"
           ad (uppterm ad [] 0 empty_env) a
           bd (uppterm ad [] ad e) b;*)
         ok := unif ad e bd a b
     | (Delayed_goal({ depth; pdiff; goal = g} as dpg), _) as exn :: rest ->
         remove_constraint exn;
         to_resume := rest;
         (*Fmt.fprintf Fmt.std_formatter
          "Resuming goal: @[<hov 2> ...@ ⊢^%d %a@]\n%!"
          (*"Resuming goal: @[<hov 2> %a@ ⊢^%d %a@]\n%!"*)
          (*(pplist (uppterm depth [] 0 empty_env) ",") pdiff*)
          depth (uppterm depth [] 0 empty_env) g ;*)
         to_be_resumed := Obj.magic dpg :: !to_be_resumed
     | _ -> anomaly "Unknown constraint type"
   done ;
   (* Phase 2: we propagate the constraints *)
   (*if !new_delayed <> [] then Fmt.fprintf Fmt.std_formatter "RESUME ALL\n%!";*)
   [%spy "resume-all" (fun fmt -> Fmt.fprintf fmt "%d") (List.length !new_delayed)];
   let history = HISTORY.create 17 in
   if !ok then begin
    while !new_delayed <> [] do
    match !new_delayed with
     | (dpg, j) :: rest ->
        (match propagate dpg j history with
          | `NoSuchJ -> new_delayed := rest
          | `NoMatch -> new_delayed := (dpg, j+1) :: rest
          | `Matched (to_be_removed,to_be_added) ->
             (*List.iter (function
                (Delayed_goal ((depth,_,_,g)),_) ->
                  Fmt.fprintf Fmt.std_formatter
                   "Killing goal: @[<hov 2> ... ⊢^%d %a@]\n%!" depth (uppterm depth [] 0 empty_env) g
              | _ -> ()) to_be_removed ;*)
             List.iter remove_constraint to_be_removed ;
             (*List.iter (fun (depth,_,_,g) ->
                  Fmt.fprintf Fmt.std_formatter
                   "Additional goal: @[<hov 2> ... ⊢^%d %a@]\n%!" depth (uppterm depth [] 0 empty_env) g)
               to_be_added ;*)
             (*List.iter add_constraint to_be_added*)
             to_be_resumed := to_be_added @ !to_be_resumed )
     | _ -> anomaly "Empty list"
    done;
    Some (List.map (fun { depth = d; prog = p; goal = g } -> d,Obj.magic p,g) (List.rev !to_be_resumed))
   end
   else None

  and next_alt alts =
   if alts == emptyalts then raise No_clause
   else
    let { program = p; clauses = clauses; goal = g; goals = gs; stack = next;
          trail = old_trail; depth = depth; lvl = lvl; next = alts} = alts in
    undo_trail old_trail;
    backchain depth p g gs clauses next alts lvl (* XXX *)
  in


 (* Finally the runtime *)
 fun () ->
  let { Fork.exec = exec ; get = get ; set = set } = Fork.fork () in
  (fun ?(pr_delay=false) ?(depth=0) p (_,argsdepth,q_env,q) chr mds ->
     set original_program p;
     set chrules chr;
     set modes mds;
     exec (fun lcs ->
     let q = move ~adepth:argsdepth ~from:depth ~to_:depth q_env q in
     let alts = run lcs p q [] FNil emptyalts emptyalts in
     if pr_delay then begin
       Fmt.fprintf Fmt.std_formatter "===== delayed ======\n%!";
       print_delayed ();
       Fmt.fprintf Fmt.std_formatter "====================\n%!";
     end;
     alts)),
  (fun ?(pr_delay=false) alts ->
     exec (fun alts -> 
       let alts = next_alt alts in
       if pr_delay then begin
         Fmt.fprintf Fmt.std_formatter "===== delayed ======\n%!";
         print_delayed ();
         Fmt.fprintf Fmt.std_formatter "====================\n%!";
       end;
       alts) alts),
  (fun () -> get delayed = [])
;;

do_make_runtime := make_runtime;;

(* }}} *)
(* {{{ ************** "compilation" + API *********************** *)

module ConstMap = Map.Make(F)

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
   let c = (F.show f).[0] in
   if ('A' <= c && c <= 'Z') || c = '_' then
     let amap, v = stack_var_of_ast amap (F.show f) in amap, v
   else amap, snd (funct_of_ast f)
;;

let desugar inner s args =
  let open Elpi_ast in
  let open Func in
  let varname = function Const x -> x | _ -> assert false in
  let last_is_arrow l =
    match List.rev l with
    | App(Const f,_) :: _ -> equal f arrowf
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
      
let rec stack_term_of_ast ?(inner=false) lvl amap cmap = function
  | Elpi_ast.Const f -> stack_funct_of_ast amap cmap f
  | Elpi_ast.Custom f ->
     let cname = fst (funct_of_ast f) in
     begin try let _f = lookup_custom cname in ()
     with Not_found -> error ("No custom named " ^ F.show f) end;
     amap, Custom (cname, [])
  | Elpi_ast.App(Elpi_ast.Const f, tl) ->
     let f, tl = desugar inner f tl in
     let amap, rev_tl =
       List.fold_left (fun (amap, tl) t ->
         let amap, t = stack_term_of_ast ~inner:true lvl amap cmap t in
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
  | Elpi_ast.App (Elpi_ast.Custom f,tl) ->
     let cname = fst (funct_of_ast f) in
     begin try let _f = lookup_custom cname in ()
     with Not_found -> error ("No custom named " ^ F.show f) end;
     let amap, rev_tl =
       List.fold_left (fun (amap, tl) t ->
          let amap, t = stack_term_of_ast ~inner:true lvl amap cmap t in
          (amap, t::tl))
        (amap, []) tl in
     amap, Custom(cname, List.rev rev_tl)
  | Elpi_ast.Lam (x,t) ->
     let cmap' = ConstMap.add x (constant_of_dbl lvl) cmap in
     let amap, t' = stack_term_of_ast ~inner:true (lvl+1) amap cmap' t in
     amap, Lam t'
  | Elpi_ast.App (Elpi_ast.App (f,l1),l2) ->
     stack_term_of_ast ~inner lvl amap cmap (Elpi_ast.App (f, l1@l2))
  | Elpi_ast.String str -> amap, String str
  | Elpi_ast.Int i -> amap, Int i 
  | Elpi_ast.Float f -> amap, Float f 
  | Elpi_ast.App (Elpi_ast.Lam _,_) -> error "Beta-redexes not in our language"
  | Elpi_ast.App (Elpi_ast.String _,_) -> type_error "Applied string value"
  | Elpi_ast.App (Elpi_ast.Int _,_) -> type_error "Applied integer value"
  | Elpi_ast.App (Elpi_ast.Float _,_) -> type_error "Applied float value"
;;

(* BUG: I pass the empty amap, that is plainly wrong.
   Therefore the function only works on meta-closed terms. *)
let term_of_ast ~depth t =
 let argsdepth = depth in
 let freevars = mkinterval 0 depth 0 in
 let cmap =
  List.fold_left (fun cmap i ->
   ConstMap.add (F.from_string (string_of_constant (destConst i))) i cmap
   ) ConstMap.empty freevars in
 let { max_arg = max; name2arg = l }, t =
  stack_term_of_ast depth empty_amap cmap t in
 let env = Array.make max dummy in
 move ~adepth:argsdepth ~from:depth ~to_:depth env t
;;

let query_of_ast_cmap lcs cmap t =
  let { max_arg = max; name2arg = l }, t =
    stack_term_of_ast lcs empty_amap cmap t in
  List.rev_map fst l, 0, Array.make max dummy, t
;;

let query_of_ast { query_depth = lcs } t =
  query_of_ast_cmap lcs ConstMap.empty t;;

let program_of_ast ?(print=false) (p : Elpi_ast.decl list) : program =
 let rec aux lcs clauses chr =
  let clauses,lcs,chr,_,cmapstack,_ =
   List.fold_left
    (fun (clauses,lcs,chr,cmap,cmapstack,clique) d ->
      match d with
         Elpi_ast.Clause t ->
          let names,_,env,t = query_of_ast_cmap lcs cmap t in
          if print then Fmt.eprintf "%a.@;" (uppterm 0 names 0 env) t;
          let moreclauses, morelcs = clausify (Array.length env) lcs t in
          let moreclauses, chr =
            List.fold_right (fun c (cls,chr) ->
               if hd_pred c == rulec then
                 match clique with
                 | None -> error "CH rules allowed only in constraint block"
                 | Some cl -> cls, CHR.add_rule cl c chr
               else c :: cls, chr 
              ) moreclauses ([],chr) in

          List.rev_append moreclauses clauses, lcs+morelcs, chr,cmap, cmapstack, clique
       | Elpi_ast.Begin -> clauses, lcs, chr,cmap, cmap::cmapstack, clique
       | Elpi_ast.Accumulated p ->
          let moreclausesrev,lcs,chr = aux lcs p chr in
           moreclausesrev@clauses, lcs, chr,cmap, cmapstack, clique
       | Elpi_ast.End ->
          (match cmapstack with
              [] ->
               (* TODO: raise it in the parser *)
               error "End without a Begin"
            | cmap::cmapstack -> clauses, lcs, chr,cmap, cmapstack, None)
       | Elpi_ast.Local v ->
          clauses,lcs+1, chr, ConstMap.add v (constant_of_dbl lcs) cmap, cmapstack, clique
       | Elpi_ast.Mode m ->
            let funct_of_ast c =
              try
                match ConstMap.find c cmap with
                | Const x -> x 
                | _ -> assert false
              with Not_found -> fst (funct_of_ast c) in
            List.iter (fun (c,l,alias) ->
             let key = funct_of_ast c in
             let mode = l in
             let alias = option_map (fun (x,s) ->
               funct_of_ast x,
               List.map (fun (x,y) -> funct_of_ast x, funct_of_ast y) s) alias
             in
             match alias with
             | None -> modes := CMap.add key (Mono mode) !modes
             | Some (a,subst) ->
                  modes := CMap.add a (Mono mode) !modes;
                  match CMap.find key !modes with
                  | Mono _ -> assert false
                  | Multi l ->
                      modes := CMap.add key (Multi ((a,subst)::l)) !modes
                  | exception Not_found ->
                      modes := CMap.add key (Multi [a,subst]) !modes
            ) m;
            clauses,lcs,chr,cmap,cmapstack,clique
       | Elpi_ast.Constraint fl ->
            let funct_of_ast c =
              try
                match ConstMap.find c cmap with
                | Const x -> x 
                | _ -> assert false
              with Not_found -> fst (funct_of_ast c) in
           if clique <> None then error "nested constraint";
           let fl = List.map (fun x -> funct_of_ast x) fl in
           let chr, clique = CHR.new_clique fl chr in
            clauses,lcs,chr,cmap,cmap::cmapstack, Some clique
    ) ([],lcs,chr,ConstMap.empty,[],None) clauses in
  if cmapstack <> [] then error "Begin without an End" else clauses,lcs,chr in
 let clausesrev,lcs,chr = aux 0 p CHR.empty in
 { query_depth = lcs;
   idx = make_index (List.rev clausesrev);
   chr;
   modes = !modes}
;;

(* RUN with non indexed engine *)
type query = string list * int * term array * term

let execute_once { query_depth = depth; idx = p; chr; modes } q =
 let run, cont, _ = make_runtime () in
 try ignore (run ~pr_delay:true p q chr modes depth) ; false
 with No_clause | Non_linear -> true
;;

let execute_loop
  { query_depth = depth; idx = p; chr; modes } ((q_names,q_argsdepth,q_env,q) as qq) 
=
 let run, cont, _ = make_runtime () in
 let k = ref emptyalts in
 let do_with_infos f x =
  let time0 = Unix.gettimeofday() in
  f x ;
  let time1 = Unix.gettimeofday() in
  prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
 (* Fmt.eprintf "Raw Result: %a\n%!" (ppterm depth q_names q_argsdepth q_env) q ;*)
  Fmt.eprintf "Result: \n%!" ;
  List.iteri (fun i name -> Fmt.eprintf "@[<hov 1>%s=%a@]\n%!" name
   (uppterm depth q_names 0 q_env) q_env.(i)) q_names;
  Fmt.eprintf "Raw result: \n%!" ;
  List.iteri (fun i name -> Fmt.eprintf "@[<hov 1>%s=%a@]\n%!" name
   (ppterm depth q_names 0 q_env) q_env.(i)) q_names;
  in
 do_with_infos (fun _ -> k := (run ~pr_delay:true p qq chr modes depth)) ();
 while !k != emptyalts do
   prerr_endline "More? (Y/n)";
   if read_line() = "n" then k := emptyalts else
    try do_with_infos (fun _ -> k := cont ~pr_delay:true !k) ()
    with No_clause -> prerr_endline "Fail"; k := emptyalts
 done
;;

(* }}} *)

(* vim: set foldmethod=marker: *)
