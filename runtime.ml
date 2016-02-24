(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Utils : sig

  val pplist : ?max:int -> ?boxed:bool ->
    (Format.formatter -> 'a -> unit) ->
    ?pplastelem:(Format.formatter -> 'a -> unit) ->
      string -> Format.formatter -> 'a list -> unit

  val smart_map : ('a -> 'a) -> 'a list -> 'a list

  (* tail rec when the two lists have len 1; raises no exception. *)
  val for_all2 : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

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
  if boxed then Format.fprintf f "@[<hov 1>";
  let args,last = match List.rev l with
    [] -> assert false;
  | head::tail -> List.rev tail,head in
  List.iteri (fun i x -> if i = max + 1 then Format.fprintf f "..."
                         else if i > max then ()
                         else Format.fprintf f "%a%s@ " ppelem x sep) args;
  Format.fprintf f "%a" pplastelem last;
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


let option_get = function Some x -> x | None -> assert false

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
  | UVar of term oref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term oref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | String of F.t
  | Int of int
  | Float of float
and 'a oref = {
  mutable contents : 'a;
  mutable rest : constraint_ list
}
and constraint_ =
 (* exn is the constraint;
    the associated list is the list of variables the constraint is
    associated to *)
 exn * term oref list (* well... open type in caml < 4.02 *)

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
  val propagatec : constant
  val consc  : constant
  val nilc   : term
  val entailsc : constant
  val nablac : constant
  val destappc : constant

  (* Value for unassigned UVar/Arg *)
  val dummy  : term

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
   Hashtbl.add h' n (F.pp x);
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
let propagatec = fst (funct_of_ast (F.from_string "propagate"))
let nilc = snd (funct_of_ast F.nilf)
let consc = fst (funct_of_ast F.consf)
let nablac = fst (funct_of_ast (F.from_string "nabla"))
let entailsc = fst (funct_of_ast (F.from_string "?-"))
let destappc = fst (funct_of_ast (F.from_string "@"))

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

  val prologppterm :
    string list -> term array -> Format.formatter -> term -> unit

  val do_deref : (from:int -> to_:int -> int -> term -> term) ref
  val do_app_deref : (from:int -> to_:int -> term list -> term -> term) ref

end = struct (* {{{ *)

let do_deref = ref (fun ~from ~to_ _ _ -> assert false);;
let do_app_deref = ref (fun ~from ~to_ _ _ -> assert false);;
let m = ref [];;
let n = ref 0;;

let min_prec = Parser.min_precedence
let appl_prec = Parser.appl_precedence
let lam_prec = Parser.lam_precedence
let inf_prec = Parser.inf_precedence

let xppterm ~nice depth0 names argsdepth env f t =
  let pp_app f pphd pparg ?pplastarg (hd,args) =
   if args = [] then pphd f hd
   else
    Format.fprintf f "@[<hov 1>%a@ %a@]" pphd hd
     (pplist pparg ?pplastelem:pplastarg "") args in
  let ppconstant f c = Format.fprintf f "%s" (string_of_constant c) in
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
     Format.fprintf f "%s%s" s
      (if vardepth=0 then "" else "^" ^ string_of_int vardepth)
   end else if nice then begin
    aux prec depth f (!do_deref ~from:vardepth ~to_:depth args !!r)
   end else Format.fprintf f "<%a>_%d" (aux 0 vardepth) !!r vardepth
  and pp_arg prec depth f n =
   let name= try List.nth names n with Failure _ -> "A" ^ string_of_int n in
   if try env.(n) == dummy with Invalid_argument _ -> true then
    Format.fprintf f "%s" name
   (* TODO: (potential?) bug here, the argument is not lifted
      from g_depth (currently not even passed to the function)
      to depth (not passed as well) *)
   else if nice then aux prec depth f (!do_deref ~from:argsdepth ~to_:depth 0 env.(n))
   else Format.fprintf f "≪%a≫ " (aux 0 argsdepth) env.(n)

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
     (Format.fprintf f "(" ; h () ; Format.fprintf f ")")
    else h () in
   match t with
   | t when nice &&
      match t with App (hd,_,_) when hd==consc -> true | _ -> t==nilc
     ->
      let prefix,last = flat_cons_to_list depth [] t in
      Format.fprintf f "[" ;
      pplist (aux Parser.list_element_prec depth) "," f prefix ;
      if last!=nilc then begin
       Format.fprintf f " | " ;
       aux prec 1 f last
      end;   
      Format.fprintf f "]"
    | Const s -> ppconstant f s 
    | App (hd,x,xs) ->
       (try
         let assoc,hdlvl =
          Parser.precedence_of (F.from_string (string_of_constant hd)) in
         with_parens hdlvl
         (fun _ -> match assoc with
            Parser.Infix when List.length xs = 1 ->
             Format.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Parser.Infixl when List.length xs = 1 ->
             Format.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux hdlvl depth) x ppconstant hd
              (aux (hdlvl+1) depth) (List.hd xs)
          | Parser.Infixr when List.length xs = 1 ->
             Format.fprintf f "@[<hov 1>%a@ %a@ %a@]"
              (aux (hdlvl+1) depth) x ppconstant hd
              (aux hdlvl depth) (List.hd xs)
          | Parser.Prefix when xs = [] ->
             Format.fprintf f "@[<hov 1>%a@ %a@]" ppconstant hd
              (aux hdlvl depth) x
          | Parser.Postfix when xs = [] ->
             Format.fprintf f "@[<hov 1>%a@ %a@]" (aux hdlvl depth) x
              ppconstant hd 
          | _ ->
             pp_app f ppconstant (aux inf_prec depth)
              ~pplastarg:(aux_last inf_prec depth) (hd,x::xs))
        with Not_found -> 
         let lastarg = List.nth (x::xs) (List.length xs) in
         let hdlvl =
          if match lastarg with Lam _ -> true | _ -> false then lam_prec
          else appl_prec in
         with_parens hdlvl (fun _ ->
          pp_app f ppconstant (aux inf_prec depth)
           ~pplastarg:(aux_last inf_prec depth) (hd,x::xs)))
    | Custom (hd,xs) ->
       with_parens appl_prec (fun _ ->
        pp_app f ppconstant (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (hd,xs))
    | UVar (r,vardepth,argsno) when not nice ->
       let args = mkinterval vardepth argsno 0 in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        Format.fprintf f "." ;
        pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant (r,args))
    | UVar (r,vardepth,argsno) when !!r == dummy ->
       let diff = vardepth - depth0 in
       let diff = if diff >= 0 then diff else 0 in
       let vardepth = vardepth - diff in
       let argsno = argsno + diff in
       let args = mkinterval vardepth argsno 0 in
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
       let args = mkinterval argsdepth argsno 0 in
       with_parens ~test:(args <> []) appl_prec (fun _ ->
        pp_app f (pp_arg prec depth) ppconstant (n,args))
    | AppArg (v,terms) ->
       with_parens appl_prec (fun _ ->
        pp_app f (pp_arg inf_prec depth) (aux inf_prec depth)
         ~pplastarg:(aux_last inf_prec depth) (v,terms))
    | Lam t ->
       with_parens lam_prec (fun _ ->
        let c = constant_of_dbl depth in
        Format.fprintf f "%a \\@ %a" (aux inf_prec depth) c
         (aux 0 (depth+1)) t)
    | String str -> Format.fprintf f "\"%s\"" (Parser.ASTFuncS.pp str)
    | Int i -> Format.fprintf f "%d" i
    | Float x -> Format.fprintf f "%f" x
  in
    try aux min_prec depth0 f t with e -> Format.fprintf f "EXN PRINTING: %s" (Printexc.to_string e)
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
        else if hd==andc || hd == andc2 then    
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
let prologppterm = xppterm_prolog ~nice:true 

end (* }}} *)
open Pp

type trail_item =
   Assign of term oref
 | AddConstr of constraint_
 | DelConstr of constraint_

type trail = trail_item list ref
let trail : trail = Fork.new_local []
let last_call = Fork.new_local false;;
let delayed = Fork.new_local []
let new_delayed = Fork.new_local []
let to_resume = Fork.new_local []

exception Delayed_unif of int * term array * int * term * term

let add_constraint0 (_,vars) as cstr =
 delayed := cstr :: !delayed;
 List.iter (fun r -> r.rest <- cstr :: r.rest) vars

let add_constraint cstr =
 add_constraint0 cstr ;
 (match cstr with
     Delayed_unif _,_ -> ()
   | _ (* Delayed_goal _ *) ->
      new_delayed := (cstr, 0) :: !new_delayed);
 if not !last_call then trail := AddConstr cstr :: !trail

let remove_constraint0 (_,vars) as cstr =
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
     (*Format.fprintf Format.std_formatter
       "@[<hov 2>%d delayed goal(s) to resume since@ %a <-@ %a@]@\n%!"
          (List.length r.rest)
          (ppterm 0 [] 0 [||]) (UVar(r,0,0))
          (ppterm 0 [] 0 [||]) v;*)
     to_resume := r.rest @ !to_resume
    end;
 r.contents <- v
;;

let oref x = { contents = x; rest = [] }


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

let def_avoid = oref dummy
let occurr_check r1 r2 = if r1 == r2 then raise RestrictionFailure

let dummy_env = [||]

let rec make_lambdas destdepth args =
 if args = 0 then let x = UVar(oref dummy,destdepth,0) in x,x
 else let x,y = make_lambdas (destdepth+1) (args-1) in Lam x, y

let rec to_heap argsdepth ~from ~to_ ?(avoid=def_avoid) e t =
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
         full_deref argsdepth ~from:vardepth ~to_ args e t
       else
         (* First phase: from vardepth to from+depth *)
         let t =
            full_deref argsdepth
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
    | Arg (i,args) ->
       let a = e.(i) in
       if a == dummy then
         let r = oref dummy in
         let m = min argsdepth to_ in
         let v = UVar(r,m,0) in
         e.(i) <- v;
         if args == 0 then v
         else if argsdepth+args <= to_ then UVar(r,m,args)
         else begin
          Format.fprintf Format.str_formatter
           "Non trivial pruning not implemented (maybe delay): t=%a, delta=%d%!"
            (ppterm depth [] argsdepth e) x delta;
          anomaly (Format.flush_str_formatter ())
         end
       else
         full_deref argsdepth
           ~from:argsdepth ~to_:(to_+depth) args e a
    | AppArg(i,args) ->
       let a = e.(i) in
       let args =
        try List.map (aux depth) args
        with RestrictionFailure ->
         Format.fprintf Format.str_formatter
          "Non trivial pruning not implemented (maybe delay): t=%a, delta=%d%!"
           (ppterm depth [] argsdepth e) x delta;
         anomaly (Format.flush_str_formatter ())
       in
       if a == dummy then
         let r = oref dummy in
         let m = min argsdepth to_ in
         let v = UVar(r,m,0) in
         e.(i) <- v;
         (*BUG/TODO: check if we can stay in the fragment *)
         AppUVar(r,m,args) 
       else
         app_deref ~from:argsdepth ~to_:(to_+depth) args a

    (* pruning *)
    | UVar (r,vardepth,argsno) when delta > 0 ->
       occurr_check avoid r;
       if vardepth+argsno <= to_ then x
       else
         let assignment,fresh = make_lambdas (to_-argsno) argsno in
         if not !last_call then
          trail := (Assign r) :: !trail;
         r @:= assignment;
        (* TODO: test if it is more efficient here to return fresh or
           the original, imperatively changed, term. The current solution
           avoids dereference chains, but puts more pressure on the GC. *)
         fresh
    | UVar (r,vardepth,argsno) ->
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
       let args =
        try List.map (aux depth) (args0@args)
        with RestrictionFailure ->
         Format.fprintf Format.str_formatter
          "Non trivial pruning not implemented (maybe delay): t=%a, delta=%d%!"
           (ppterm depth [] argsdepth e) x delta;
         anomaly (Format.flush_str_formatter ())
       in
       AppUVar (r,vardepth,args)

    | AppUVar _ ->
       Format.fprintf Format.str_formatter
        "Non trivial pruning not implemented (maybe delay): t=%a, delta=%d%!"
         (ppterm depth [] argsdepth e) x delta;
       anomaly (Format.flush_str_formatter ())
  in
    let rc = aux 0 t in
    SPY "heap-term" (ppterm to_ [] argsdepth e) rc;
    rc

(* full_deref performs lifting only and with from <= to
   if called on non-heap terms, it does not turn them to heap terms
   (if from=to_)

   Note:
     when full_deref is called inside restrict, it may be from > to_
     t lives in from; args already live in to_
*)
and full_deref argsdepth ~from ~to_ args e t =
  TRACE "full_deref" (fun fmt ->
    Format.fprintf fmt "full_deref from:%d to:%d %a @@ %d"
      from to_ (ppterm from [] 0 e) t args)
 if args == 0 then
   if from == to_ then t
   else to_heap argsdepth ~from ~to_ e t
 else (* O(1) reduction fragment tested here *)
   let from,args',t = eat_args from args t in
   let t = full_deref argsdepth ~from ~to_ 0 e t in
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
 TRACE "lift" (fun fmt ->
   Format.fprintf fmt "@[<hov 1>from:%d@ to:%d@ %a@]"
     from to_ (uppterm from [] 0 [||]) t)
 (* Dummy trail, argsdepth and e: they won't be used *)
 if from == to_ then t
 else to_heap 0 ~from ~to_ dummy_env t

(* Deref is to be called only on heap terms and with from <= to *)
and deref ~from ~to_ args t =
 (* Dummy trail, argsdepth and e: they won't be used *)
 full_deref 0 ~from ~to_ args dummy_env t

(* UVar(_,from,argsno) -> Uvar(_,to_,argsno+from-to_) *)
and decrease_depth r ~from ~to_ argsno =
 if from <= to_ then r,from,argsno
 else
  let newr = oref dummy in
  let newargsno = argsno+from-to_ in
  let newvar = UVar(newr,to_,newargsno) in
  (* TODO: here we are not registering the operation in the
     trail to avoid passing last_call/trail around in every single
     function. Decrease_depth is reversible. However, does this slow
     down? Would using a global last_call/trail speed up things? What
     about passing around last_call/trail? *)
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
 TRACE "subst" (fun fmt ->
   Format.fprintf fmt "@[<hov 2>t: %a@ ts: %a@]"
   (uppterm (fromdepth+1) [] 0 [||]) t (pplist (uppterm 0 [] 0 [||]) ",") ts)
 if ts == [] then t
 else
   let len = List.length ts in
   let fromdepthlen = fromdepth + len in
   let rec aux depth tt =
   TRACE "subst-aux" (fun fmt ->
     Format.fprintf fmt "@[<hov 2>t: %a@]" (uppterm (fromdepth+1) [] 0 [||]) tt)
   match tt with
   | Const c as x ->
      if c >= fromdepth && c < fromdepthlen then
        match List.nth ts (len-1 - (c-fromdepth)) with
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
        match List.nth ts (len-1 - (c-fromdepth)) with
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
      TCALL aux depth (deref ~from:vardepth ~to_:depth argsno g)
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
      TCALL aux depth (app_deref ~from:vardepth ~to_:depth args t)
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
 TRACE "beta" (fun fmt ->
   Format.fprintf fmt "@[<hov 2>subst@ t: %a@ args: %a@]"
     (uppterm depth [] 0 [||]) t (pplist (uppterm depth [] 0 [||]) ",") args)
 match t,args with
 | Lam t',hd::tl -> TCALL beta depth (hd::sub) t' tl
 | _ ->
    let t' = subst depth sub t in
    SPY "subst-result" (ppterm depth [] 0 [||]) t';
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
let restrict ?avoid argsdepth ~from ~to_ e t =
 if from = to_ && avoid == None then t
 else to_heap ?avoid argsdepth ~from ~to_ e t

(* }}} *)

type 'key clause =
 { depth : int; args : term list; hyps : term list; vars : int; key : 'key }

 
(* {{{ ************** indexing ********************************** *)

module type Indexing = sig

  type key
  val pp_key : key -> string
  type index
  val key_of : mode:[`Query | `Clause] -> depth:int -> term -> key
  val add_clauses : key clause list -> index -> index
  val get_clauses : depth:int -> term -> index -> key clause list
  val make_index : key clause list -> index
  val diff_progs : to_:int -> index -> index -> term list
end

module TwoMapIndexing : Indexing = struct (* {{{ *)

(* all clauses: used when the query is flexible
   all flexible clauses: used when the query is rigid and the map
                        for that atom is empty
   map: used when the query is rigid before trying the all flexible clauses *)
type key1 = int
type key2 = int
type key = key1 * key2

let pp_key (hd,_) = string_of_constant hd

type index = (key clause list * key clause list * key clause list Ptmap.t) Ptmap.t

let variablek =    -99999999
let abstractionk = -99999998

let key_of ~mode:_ ~depth =
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

let get_clauses ~depth a m =
 let ind,app = key_of ~mode:`Query ~depth a in
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

let make_index p = add_clauses (List.rev p) Ptmap.empty
 
(* flatten_snd = List.flatten o (List.map ~~snd~~) *)
(* TODO: is this optimization necessary or useless? *)
let rec flatten_snd =
 function
    [] -> []
  | (_,(hd,_,_))::tl -> hd @ flatten_snd tl 

let diff_progs ~to_ (prog1 : index) prog2 =  
 let res =
  flatten_snd
   (Ptmap.to_list
    (Ptmap.diff
      (fun (cllist1,dummy1,dummy2) (cllist2,_,_) ->        
        let rec get_prefix acc =
         function
            l when l == cllist2 -> List.rev acc
          | hd::tl -> get_prefix (hd::acc) tl
          | [] -> anomaly "Some clauses were deleted from the program" in
        match get_prefix [] cllist1 with
           [] -> None
         | l -> Some (l,dummy1,dummy2))
      prog1 prog2)) in
 List.rev_map
  (fun { depth = depth; args = args; hyps = hyps; key=(key,_) } ->
    let app = match args with [] -> Const key | hd::tl -> App (key,hd,tl) in
    lift ~from:depth ~to_ app
  ) res

end (* }}} *)

module UnifBits : Indexing = struct

  type key = int

  type index = (key clause * int) list Ptmap.t  (* timestamp *)

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
      TRACE "set-section" (fun fmt -> Format.fprintf fmt "@[<hv 0>%s@ %s@]"
        (dec_to_bin !buf) (dec_to_bin new_bits))
      buf := new_bits lor !buf in
    let rec index lvl tm depth left right =
      TRACE "index" (fun fmt -> Format.fprintf fmt "@[<hv 0>%a@]"
        (uppterm depth [] 0 [||]) tm)
      match tm with
      | Const k | Custom (k,_) ->
          set_section (if lvl=0 then k else hash k) left right 
      | UVar ({contents=t},origdepth,args) when t != dummy ->
         index lvl (deref ~from:origdepth ~to_:depth args t) depth left right
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
     and subindex lvl depth j left step = function
       | [] -> ()
       | x::xs ->
          let j2 = j + step in
          index (lvl+1) x depth j2 j;
          if j2 + step <= left then subindex lvl depth j2 left step xs
    in
      index 0 term depth key_bits 0;
      SPY "key-val" (fun f x -> Format.fprintf f "%s" (dec_to_bin x)) (!buf);
      !buf

  let get_clauses ~depth a m =
    let ind = key_of ~mode:`Query ~depth a in
    let cl_list = List.flatten (Ptmap.find_unifiables ~functor_bits ind m) in
    List.map fst
      (List.fast_sort (fun (_,cl1) (_,cl2) -> compare cl1 cl2) cl_list)
      
  let timestamp = ref 0    
  let add_clauses ?(op=decr) clauses ptree =
    List.fold_left (fun m clause -> 
      let ind = clause.key in
      let clause = clause, !timestamp in
      op timestamp;
      try 
        let cl_list = Ptmap.find ind m in
        Ptmap.add ind (clause::cl_list) m
      with Not_found -> 
        Ptmap.add ind [clause] m
    ) ptree clauses
 
  let make_index p =
    timestamp := 1;
    let m = add_clauses ~op:incr p Ptmap.empty in
    timestamp := 0;
    m

  (* Get rid of optional arg *)
  let add_clauses cl pt = add_clauses cl pt

  (* from (key, (key clause * int) list) list  
    creates  key clause list *)
  let rec flatten_ = function
     [] -> []
   | (_,l)::tl -> (List.map (fun (cl,_) -> cl) l) @ flatten_ tl

  let diff_progs ~to_ (prog1 : index) prog2 =
   assert false (* TO BE IMPLEMENTED BUT IT CAN ONLY BE IMPLEMENTED
                   AUGMENTING THE DATA STRUCTURES *)

end

(* }}} *)
  
(* open UnifBits *)
open TwoMapIndexing

let ppclause f { args = args; hyps = hyps; key = hd } =
  Format.fprintf f "@[<hov 1>%s %a :- %a.@]" (pp_key hd)
     (pplist (uppterm 0 [] 0 [||]) "") args
     (pplist (uppterm 0 [] 0 [||]) ",") hyps

(* {{{ ************** unification ******************************* *)

type index = TwoMapIndexing.index
type program = int * index (* int is the depth, i.e. number of
                              sigma/local-introduced variables *)
type goal = (*depth:*)int * index * term

let original_program = Fork.new_local (Obj.magic 0 : index) (* dummy value *)

(* Delayed_goal of (depth, orig_prog, diffed_prog, goal), everything lives in
 * depth (but for orig_prog) *)
(* CAVEAT: we are going to use pointer equality on the contents, so it must
 * be a tuple *)
exception Delayed_goal of (int * index * term list * term)

let delay_goal ~depth prog ~goal:g ~on:keys =
  let pdiff = diff_progs ~to_:depth prog !original_program in
  (*Format.fprintf Format.std_formatter
    "Delaying goal: @[<hov 2> %a@ ⊢ %a@]\n%!"
      (pplist (uppterm depth [] 0 [||]) ",") pdiff
      (uppterm depth [] 0 [||]) g ;*)
  let delayed_goal = (Delayed_goal (depth,prog,pdiff,g), keys) in
  add_constraint delayed_goal
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
   + we deref to move everything to a/bdepth + depth
   
   Note about dereferencing Arg(i,args):
   - args live *here* (bdepth + depth)
   - e.(i) lives in bdepth
   + we deref to move everything to adepth + depth
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
        get_con (deref ~from ~to_ args t)
    | AppUVar ({ contents = t }, from, args) when t != dummy -> 
        get_con (app_deref ~from ~to_ args t)
    | Arg (i,args) when e.(i) != dummy ->
        get_con (deref ~from:adepth ~to_ args e.(i))
    | AppArg (i,args) when e.(i) != dummy -> 
        get_con (app_deref ~from:adepth ~to_ args e.(i))
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
  SPY "is_llam" (fun fmt (b,map) -> Format.fprintf fmt "%d + %a = %b, %a"
    lvl (pplist (ppterm adepth [] bdepth e) "") args b
    (pplist (fun fmt (x,n) -> Format.fprintf fmt "%d |-> %d" x n) "") map) res;
  res

let mkAppUVar r lvl l =
  try UVar(r,lvl,in_fragment lvl l)
  with NotInTheFragment -> AppUVar(r,lvl,l)

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
  (* lift = false makes the code insensitive to left/right, i.e. no lift from b
   * to a is performed *)
  let cst ?(lift=true) c b delta = (* The complex thing (DBL) *)
    if left then begin
      if c < gamma && c < b then c
      else
        let c = if lift then c + delta else c in
        if c < gamma then c
        else if c >= a + d then c + new_lams - (a+d - gamma)
        else pos c + gamma
    end else begin
      if c < gamma then c
      else if c >= a + d then c + new_lams - (a+d - gamma)
      else pos c + gamma
    end in
  let cst ?lift c b delta =
    let n = cst ?lift c b delta in
    SPY "cst" (fun fmt (n,m) -> Format.fprintf fmt
      "%d -> %d (c:%d b:%d gamma:%d delta:%d d:%d)" n m c b gamma delta d)
      (c,n);
    n in
  let rec bind b delta w t = TRACE "bind" (fun fmt -> Format.fprintf fmt
      "%b %d + %a = t:%a a:%d delta:%d d:%d w:%d b:%d" left gamma
      (pplist (fun fmt (x,n) -> Format.fprintf fmt "%a |-> %d"
        (ppterm a [] b e) (constant_of_dbl x) n) "") l
      (ppterm a [] b [||]) t a delta d w b)
    match t with
    | UVar (r1,_,_) | AppUVar (r1,_,_) when r == r1 -> raise RestrictionFailure
    | Const c -> let n = cst c b delta in if n < 0 then constant_of_dbl n else Const n
    | Lam t -> Lam (bind b delta (w+1) t)
    | App (c,t,ts) -> App (cst c b delta, bind b delta w t, List.map (bind b delta w) ts)
    | Custom (c, tl) -> Custom(c, List.map (bind b delta w) tl)
    | String _ | Int _ | Float _ -> t
    (* deref *)
    | Arg (i,args) when e.(i) != dummy ->
        bind a 0 w (deref ~from:a ~to_:(a+d+w) args e.(i))
    | AppArg (i,args) when e.(i) != dummy ->
        bind a 0 w (app_deref ~from:a ~to_:(a+d+w) args e.(i))
    | UVar ({ contents = t }, from, args) when t != dummy ->
        bind b delta w (deref ~from ~to_:((if left then b else a)+d+w) args t)
    | AppUVar ({ contents = t }, from, args) when t != dummy ->
        bind b delta w (app_deref ~from ~to_:((if left then b else a)+d+w) args t)
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
                      (constant_of_dbl i, constant_of_dbl (cst ~lift:false i b delta))
                        :: keep_cst_for_lvl rest in
              List.split (keep_cst_for_lvl (List.sort compare l)) in
            let r' = oref dummy in
            r @:= mknLam n_args (mkAppUVar r' gamma args_gamma_lvl_abs);
            if not !last_call then trail := (Assign r) :: !trail;
            mkAppUVar r' gamma args_gamma_lvl_here
          else
            (* given that we need to make lambdas to prune some args,
             * we also permute to make the restricted meta eventually
             * fall inside the small fragment (sort the args) *)
            let args = List.sort compare args in
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
  in
  try
    r @:= mknLam new_lams (bind b delta 0 t);
    if not !last_call then trail := (Assign r) :: !trail;
    SPY "assign(HO)" (ppterm gamma [] a [||]) (!!r);
    true
  with RestrictionFailure -> false
;;

let unif adepth e bdepth a b =

 (* heap=true if b is known to be a heap term *)
 let rec unif depth a bdepth b heap =
   TRACE "unif" (fun fmt ->
     Format.fprintf fmt "@[<hov 2>^%d:%a@ =%d= ^%d:%a@]%!"
       adepth (ppterm (adepth+depth) [] adepth [||]) a depth
       bdepth (ppterm (bdepth+depth) [] adepth e) b)
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
       restrict adepth ~from:(adepth+depth) ~to_:adepth e a;
      SPY "assign" (ppterm depth [] adepth [||]) (e.(i)); true
   | _, UVar (r,origdepth,0) ->
       if not !last_call then
        trail := (Assign r) :: !trail;
       begin try
         let t =
           if depth = 0 then
             restrict ~avoid:r adepth 
               ~from:adepth ~to_:origdepth e a
           else
             (* First step: we restrict the l.h.s. to the r.h.s. level *)
             let a =
               to_heap ~avoid:r adepth 
                 ~from:adepth ~to_:bdepth e a in
             (* Second step: we restrict the l.h.s. *)
             to_heap adepth 
               ~from:(bdepth+depth) ~to_:origdepth e a in
         r @:= t;
         SPY "assign" (ppterm depth [] adepth [||]) t; true
       with RestrictionFailure -> false end
   | UVar (r,origdepth,0), _ ->
       if not !last_call then
        trail := (Assign r) :: !trail;
       begin try
         let t =
           if depth=0 then
             if origdepth = bdepth && heap then b
             else
               to_heap ~avoid:r adepth 
                 ~from:bdepth ~to_:origdepth e b
           else
             (* First step: we lift the r.h.s. to the l.h.s. level *)
             let b =
               to_heap ~avoid:r adepth 
                 ~from:bdepth ~to_:adepth e b in
             (* Second step: we restrict the r.h.s. *)
             to_heap adepth 
               ~from:(adepth+depth) ~to_:origdepth e b in
         r @:= t;
         SPY "assign" (ppterm depth [] adepth [||]) t; true
       with RestrictionFailure -> false end

   (* simplify *)
   (* TODO: unif->deref case. Rewrite the code to do the job directly? *)
   | _, Arg (i,args) ->
      e.(i) <- fst (make_lambdas adepth args);
      SPY "assign" (ppterm depth [] adepth [||]) (e.(i));
      unif depth a bdepth b heap
   | _, UVar (r,origdepth,args) ->
      if not !last_call then
       trail := (Assign r) :: !trail;
      r @:= fst (make_lambdas origdepth args);
      SPY "assign" (ppterm depth [] adepth [||]) (!!r);
      unif depth a bdepth b heap
   | UVar (r,origdepth,args), _ ->
      if not !last_call then
       trail := (Assign r) :: !trail;
      r @:= fst (make_lambdas origdepth args);
      SPY "assign" (ppterm depth [] adepth [||]) (!!r);
      unif depth a bdepth b heap

   (* HO *)
   | other, AppArg(i,args) ->
       let is_llam, args = is_llam adepth args adepth bdepth depth false e in
       if is_llam then
         let r = oref dummy in
         e.(i) <- UVar(r,adepth,0);
         bind r adepth args adepth depth delta bdepth false other e
       else begin
       Format.fprintf Format.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth [||]) a (uppterm depth [] bdepth e) b ;
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
   | AppUVar (r, lvl,args), other ->
       let is_llam, args = is_llam lvl args adepth bdepth depth true e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth true other e
       else begin
       Format.fprintf Format.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth [||]) a (uppterm depth [] bdepth [||]) b ;
       let delayed_goal = Delayed_unif (adepth+depth,e,bdepth+depth,a,b) in
       let (_,vars) as delayed_goal =
        match is_flex other with
           None -> delayed_goal, [r]
         | Some r' -> delayed_goal, [r;r'] in
       List.iter (fun r -> r.rest <- delayed_goal :: r.rest) vars ;
       delayed := delayed_goal :: !delayed;
       true
       end
   | other, AppUVar (r, lvl,args) ->
       let is_llam, args = is_llam lvl args adepth bdepth depth false e in
       if is_llam then
         bind r lvl args adepth depth delta bdepth false other e
       else begin
       Format.fprintf Format.std_formatter "HO unification delayed: %a = %a\n%!" (uppterm depth [] adepth [||]) a (uppterm depth [] bdepth e) b ;
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
   | Float s1, Float s2 -> s1 = s2
   | String s1, String s2 -> s1==s2
   | _ -> false in
 let res = unif 0 a bdepth b false in
 SPY "unif result" (fun fmt x -> Format.fprintf fmt "%b" x) res;
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
  | _ -> error "not a list"
;;

let rec list_to_lp_list = function
  | [] -> nilc
  | x::xs -> App(consc,x,[list_to_lp_list xs])
;;

(* BUG: the following clause is rejected because (Z c d) is not
   in the fragment. However, once X and Y becomes arguments, (Z c d)
   enters the fragment. 
r :- (pi X\ pi Y\ q X Y :- pi c\ pi d\ q (Z c d) (X c d) (Y c)) => ... *)

(* Takes the source of an implication and produces the clauses to be added to
 * the program and the number of existentially quantified constants turned
 * into globals.
 *)
let rec clausify vars depth hyps ts lcs = function
(*g -> Format.eprintf "CLAUSIFY %a %d %d\n%!" (ppterm (depth+List.length ts) [] 0 [||]) g depth (List.length ts); match g with*)
  | App(c, g, gs) when c == andc || c == andc2 ->
     let res = clausify vars depth hyps ts lcs g in
     List.fold_right
      (fun g (clauses,lcs) ->
        let moreclauses,lcs = clausify vars depth hyps ts lcs g in
         clauses@moreclauses,lcs
      ) gs res
  | App(c, g2, [g1]) when c == rimplc ->
     clausify vars depth ((ts,g1)::hyps) ts lcs g2
  | App(c, _, _) when c == rimplc -> assert false
  | App(c, g1, [g2]) when c == implc ->
     clausify vars depth ((ts,g1)::hyps) ts lcs g2
  | App(c, _, _) when c == implc -> assert false
  | App(c, Lam b, []) when c == sigmac ->
     let args =
      List.rev (List.filter (function (Arg _) -> true | _ -> false) ts) in
     let cst =
      match args with
         [] -> Const (depth+lcs)
       | hd::rest -> App (depth+lcs,hd,rest) in
     clausify vars depth hyps (cst::ts) (lcs+1) b
  | App(c, Lam b, []) when c == pic ->
     clausify (vars+1) depth hyps (Arg(vars,0)::ts) lcs b
  | Const _
  | App _ as g ->
     let hyps =
      List.(flatten (rev_map (fun (ts,g) ->
         let g = lift ~from:depth ~to_:(depth+lcs) g in
         let g = subst (depth+lcs) ts g in
          split_conj g
        ) hyps)) in
     let g = lift ~from:depth ~to_:(depth+lcs) g in
     let g = subst (depth+lcs) ts g in
     (*Format.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
      (ppterm (depth+lcs) [] 0 [||]) g
      (pplist (ppterm (depth+lcs) [] 0 [||]) " , ")
      hyps ;*)
     let args =
      match g with
         Const _ -> []
       | App(_,x,xs) -> x::xs
       | Arg _ | AppArg _ -> assert false 
       | Lam _ | Custom _ | String _ | Int _ | Float _ -> assert false
       | UVar _ | AppUVar _ -> assert false
     in
      [ { depth = depth+lcs ; args= args; hyps = hyps;
          vars = vars; key=key_of ~mode:`Clause ~depth:(depth+lcs) g} ], lcs
  | UVar ({ contents=g },from,args) when g != dummy ->
     clausify vars depth hyps ts lcs
       (deref ~from ~to_:(depth+List.length ts) args g)
  | AppUVar ({contents=g},from,args) when g != dummy -> 
     clausify vars depth hyps ts lcs
       (app_deref ~from ~to_:(depth+List.length ts) args g)
  | Arg _ | AppArg _ -> anomaly "clausify called on non-heap term"
  | Lam _ | Custom _ | String _ | Int _ | Float _ ->
     error "Assuming a custom or string or int or float or function"
  | UVar _ | AppUVar _ -> error "Flexible assumption"
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
 (fun s ->
    if s = "" || s.[0] <> '$' then
      anomaly ("Custom predicate name " ^ s ^ " must begin with $");
    Hashtbl.add customs (fst (funct_of_ast (F.from_string s)))),
 Hashtbl.find customs
;;

let do_make_runtime : (unit -> (?depth:int -> 'a -> 'b -> int -> 'k) * 'c * 'd) ref =
 ref (function () -> anomaly "do_make_runtime not initialized")

exception NoMatch

let rec list_assq1 p = function
  | [] -> raise Not_found
  | ((r,_), data) :: _ when r == p -> data
  | _ :: rest -> list_assq1 p rest
;;

let rec freeze m = function
  | UVar( { contents = t} , 0,0) when t != dummy -> freeze m t
  | UVar( { contents = t} , _,_) when t != dummy -> assert false
  | AppUVar ( { contents = t }, _, _) when t != dummy -> assert false
  | UVar( r, lvl, ano) ->
     let m, (c, n) =
      (try m, list_assq1 r m
       with Not_found ->
         let n, x = new_fresh_constant () in
         ((r,lvl),(x,n)) :: m, (x,n)) in
     m, (match List.map constant_of_dbl (mkinterval 0 (lvl+ano) 0) with
        | [] -> c
        | [x] -> App(n,x,[])
        | x::xs -> App(n,x,xs))
  | AppUVar( r, lvl, args ) ->
     let m, (c, n) =
      (try m, list_assq1 r m
       with Not_found ->
         let n, x = new_fresh_constant () in
         ((r,lvl),(x,n)) :: m, (x,n)) in
     let m, args = List.fold_right (fun x (m,l) ->
        let m, x = freeze m x in
        (m, x ::l)) args (m,[]) in
     m, (match List.map constant_of_dbl (mkinterval 0 lvl 0) @ args with
        | [] -> c
        | [x] -> App(n,x,[])
        | x::xs -> App(n,x,xs))
  | App(c,x,xs) ->
      let m, x = freeze m x in
      let m, xs = List.fold_right (fun x (m,l) ->
        let m, x = freeze m x in
        (m, x ::l)) xs (m,[]) in
      m, App(c,x,xs)
  | Const _ as x -> m, x
  | Arg _ | AppArg _ -> anomaly "freeze: not an heap term"
  | Lam t -> let m, t = freeze m t in m, Lam t
  | (Int _ | Float _ | String _) as x -> m, x
  | Custom(c,xs) ->
      let m, xs = List.fold_right (fun x (m,l) ->
        let m, x = freeze m x in
        (m, x ::l)) xs (m,[]) in
      m, Custom(c,xs)
;;

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
  let rec aux m a b =
  TRACE "matching" (fun fmt ->
   Format.fprintf fmt "%a = %a" (ppterm 0 [] 0 e) a (ppterm 0 [] 0 e) b)
  match a,b with
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
  in
    aux m a b
;;

let thaw max_depth e m t =
  let rec aux = function
  | UVar( { contents = t} , lvl, ano) when t != dummy ->
      aux (deref ~from:lvl ~to_:max_depth ano t)
  | AppUVar( { contents = t} , lvl, args) when t != dummy ->
      aux (app_deref ~from:lvl ~to_:max_depth args t)
  | Arg(i, ano) when e.(i) != dummy ->
      aux (deref ~from:max_depth ~to_:max_depth ano e.(i))
  | AppArg(i, args) when e.(i) != dummy ->
      aux (app_deref ~from:max_depth ~to_:max_depth args e.(i))
  | Arg(i,ano) -> e.(i) <- UVar(oref dummy,max_depth,ano); e.(i)
  | AppArg(i,args) ->
      e.(i) <- AppUVar(oref dummy,max_depth,List.map aux args); e.(i)
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
         AppUVar(r, lvl, List.map (aux) xs)
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
  | AppUVar(r,lvl,args) -> AppUVar(r,lvl,List.map (aux) args)
  | UVar _ as x -> x
  in
    aux t
;;

let thaw max_depth e m t =
  SPY "thaw-in"  (ppterm 0 [] 0 e) t;
  let t' = thaw max_depth e m t in
  SPY "thaw-out"  (ppterm 0 [] 0 e) t';
  t'

module HISTORY = Hashtbl.Make(struct
  type t = key clause * constraint_ list
  let hash = Hashtbl.hash
  let equal (p,lp) (p',lp') = p == p' && for_all2 (==) lp lp'
end)

(* lift a term possibly containing Args *)
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
  | UVar _ -> assert false
  | AppUVar _ -> assert false
  | Custom(c,xs) -> Custom(c,List.map aux xs)
  | (String _ | Int _ | Float _) as x -> x
  in
    aux t
;;

(* constr is a new_delayed constraint;
   the two lists in output are the constraints to be removed and added *)
let propagate constr j history =
 let sequent_of_constr constr =
  match constr with
     Delayed_unif _,_ ->
      anomaly "Delayed unifications should not become new_delayed"
   | Delayed_goal (depth,_,p,t),_ -> depth,p,t
   | _ -> anomaly "Unknown constraint type" in
 let rec find_entails max_depth n = function
   | Lam t -> find_entails max_depth (n+1) t
   | App(c,x,[g]) when c == entailsc -> n, x, g
   | t -> assert false (*n, SHOULD BE AN Arg UVar(oref dummy,max_depth,0), t*) in
 let sequent_of_pattern max_depth = function
   | App(c,x,[]) when c == nablac ->
       let min_depth, ctx, g = find_entails max_depth 0 x in
       (min_depth, ctx, g)
   | Lam _ -> error "syntax error in propagate"
   | x -> 
       let min_depth, ctx, g = find_entails max_depth 0 x in
       (min_depth, ctx, g) in
 (*Format.fprintf Format.std_formatter "PROPAGATION %d\n%!" j;*)
 let query =
  let dummyv = UVar (oref dummy, 0, 0) in
   App(propagatec,dummyv,[dummyv ; dummyv]) in
 (* CSC: INVARIANT: propagate clauses can never be assumed using
    implication. Otherwise ~depth:0 is wrong and I do not see any
    reasonable semantics (i.e. a semantics where the scoping is not
    violated). For the same reason I took the propagate clauses from
    the !original_program. *)
 let p = !original_program in
 let rules = get_clauses ~depth:0 query p in


 let run,_,no_delayed = !do_make_runtime () in
 let no_such_j = ref true in
 let result =
    map_exists (function ({ (*depth : int; *) args = [ g1; g2; g3];
                     hyps = hyps; vars = nargs; key = k } as clause) ->

    let gg1 = lp_list_to_list g1 in
    let gg2 = lp_list_to_list g2 in
    let leng1 = List.length gg1 in

    let headsno = leng1 + List.length gg2 in
    if headsno < 1 then error "no heads in propagate" ;
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

     (*Format.fprintf Format.std_formatter "COMBINATIONS %d\n%!"
       (List.length combinations);*)
     
    let combinations =
      combinations |> List.map (fun l ->
        let before, after = partition_i (fun i _ -> i < j) l in
        before @ constr :: after
        ) in

     combinations |> map_exists (fun heads ->
      let hitem = clause,heads in
      no_such_j := false;
      if HISTORY.mem history hitem then begin
        Format.fprintf Format.std_formatter "pruned\n%!" ;
        None
        end
      else
       let () = HISTORY.add history hitem () in
       let heads_sequent = List.map sequent_of_constr heads in
       let max_depth =
         List.fold_left (fun acc (d,_,_) -> max d acc) 0 heads_sequent in
       let contexts, goals_at_max_depth =
         List.fold_right (fun (d,p,g) (ctxs, gs) ->
           (d,p) :: ctxs, lift ~from:d ~to_:max_depth g :: gs)
           heads_sequent ([],[]) in

       let to_match, to_remove =
         partition_i (fun i _ -> i < leng1) goals_at_max_depth in
       let _, heads_to_remove =
         partition_i (fun i _ -> i < leng1) heads in

       let lift_pattern_sequent (d,ctx,g) =
         if d > max_depth then raise NoMatch;
         d, ctx, lift_pat ~from:d ~to_:max_depth g in

       try
         let sequent_of_pattern = sequent_of_pattern max_depth in
         let patterns_sequent1 =
           List.(gg1 |> map sequent_of_pattern |> map lift_pattern_sequent) in
         let patterns_sequent2 =
           List.(gg2 |> map sequent_of_pattern |> map lift_pattern_sequent) in

         let e = Array.make nargs dummy in
         (*Format.fprintf Format.std_formatter "attempt: %a = %a\n%!"
           (pplist (uppterm max_depth [] 0 [||]) ",") (to_match @ to_remove)
           (pplist (fun fmt (_,_,g) ->
              uppterm max_depth [] 0 e fmt g) ",")
           (patterns_sequent1 @ patterns_sequent2);*)
         let match_p m t (d,_,g) = matching e max_depth (max_depth-d) m t g in
         let m = List.fold_left2 match_p [] to_match  patterns_sequent1 in
         let m = List.fold_left2 match_p m  to_remove patterns_sequent2 in
         (* check all aligned max_depth *)
         let contexts_at_max_depth = contexts |>
           List.map (fun (d,p) -> List.map (lift ~from:d ~to_:max_depth) p) in
         let ctxs_to_match, ctxs_to_remove =
           partition_i (fun i _ -> i < leng1) contexts_at_max_depth in

         let match_ctx m lt (d,ctx,_) =
           let t = list_to_lp_list lt in
           matching e max_depth (max_depth-d) m t ctx in
         let m = List.fold_left2 match_ctx m ctxs_to_match  patterns_sequent1 in
         let m = List.fold_left2 match_ctx m ctxs_to_remove patterns_sequent2 in
         
         let gg3 = lift_pat ~from:0 ~to_:max_depth g3 in
         match hyps with
         | [] -> Format.fprintf Format.std_formatter "Empty guard\n%!";
                 Some(heads_to_remove,[(max_depth,p,[],thaw max_depth e m gg3)])
         | h1 :: hs ->
            let query = [],max_depth,e,App(andc,h1,hs) in
            (*Format.fprintf Format.std_formatter "Starting runtime\n%!";*)
            (try
              (* CSC: I am not at all sure about the second occurrence of
                 max_depth below *)
              let _ = run ~depth:max_depth p query max_depth in
              if not (no_delayed ()) then begin
                anomaly "propagation rules must not $delay"
              end;
              (*Format.fprintf Format.std_formatter "Ending runtime (ok)\n%!";*)
              Some(heads_to_remove,[(max_depth,p,[],thaw max_depth e m gg3)])
            with No_clause ->
              Format.fprintf Format.std_formatter "Ending runtime (fail)\n%!";
              None)
       with NoMatch -> (*Format.fprintf Format.std_formatter "NoMatch\n%!";*)None)
     | _ -> anomaly "propagate expects 3 args") rules
 in
 match result with
 | Some x -> `Matched x
 | None when !no_such_j -> `NoSuchJ
 | _ -> `NoMatch
;;

let print_delayed () =
 List.iter
  (function
   | Delayed_unif (ad,e,bd,a,b),l ->
      Format.fprintf Format.std_formatter
       "delayed goal: @[<hov 2>^%d:%a@ == ^%d:%a on %a@]\n%!"
        ad (uppterm ad [] 0 [||]) a
        bd (uppterm ad [] ad e) b
        (pplist (uppterm ad [] 0 [||]) ",")
        (List.map (fun r -> UVar(r,0,0)) l)
   | Delayed_goal (depth,_,pdiff,g),l ->
      Format.fprintf Format.std_formatter
        "delayed goal: @[<hov 2> %a@ ⊢ %a on %a@]\n%!"
          (pplist (uppterm depth [] 0 [||]) ",") pdiff
          (uppterm depth [] 0 [||]) g
          (pplist (uppterm depth [] 0 [||]) ",")
          (List.map (fun r -> UVar(r,0,0)) l)
       (* CSC: Bug here: print at the right precedence *)
   | _ -> assert false) !delayed

(* The block of recursive functions spares the allocation of a Some/None
 * at each iteration in order to know if one needs to backtrack or continue *)
let make_runtime : unit -> (?depth:int -> 'a -> 'b -> int -> 'k) * ('k -> 'k) * (unit -> bool) =

  (* Input to be read as the orl (((p,g)::gs)::next)::alts
     depth >= 0 is the number of variables in the context. *)
  let rec run depth p g gs (next : frame) alts lvl =
    TRACE "run" (fun fmt -> ppterm depth [] 0 [||] fmt g)
 match resume_all () with
  None ->
begin Format.fprintf Format.std_formatter "Undo triggered by goal resumption\n%!";
  TCALL next_alt alts
end
 | Some ((ndepth,p,ng)::goals) ->
    run ndepth p ng (goals@(depth,p,g)::gs) next alts lvl
 | Some [] ->
    match g with
    | c when c == cutc -> TCALL cut p gs next alts lvl
    | App(c, g, gs') when c == andc || c == andc2 ->
       run depth p g (List.map(fun x -> depth,p,x) gs'@gs) next alts lvl
    | App(c, g2, [g1]) when c == rimplc ->
       (*Format.eprintf "RUN: %a\n%!" (uppterm depth [] 0 [||]) g ;*)
       let clauses, lcs = clausify 0 depth [] [] 0 g1 in
       let g2 = lift ~from:depth ~to_:(depth+lcs) g2 in
       (*Format.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 [||]) g2;*)
       run (depth+lcs) (add_clauses clauses p) g2 gs next alts lvl
    | App(c, g1, [g2]) when c == implc ->
       (*Format.eprintf "RUN: %a\n%!" (uppterm depth [] 0 [||]) g ;*)
       let clauses, lcs = clausify 0 depth [] [] 0 g1 in
       let g2 = lift ~from:depth ~to_:(depth+lcs) g2 in
       (*Format.eprintf "TO: %a \n%!" (uppterm (depth+lcs) [] 0 [||]) g2;*)
       run (depth+lcs) (add_clauses clauses p) g2 gs next alts lvl
(*  This stays commented out because it slows down rev18 in a visible way!   *)
(*  | App(c, _, _) when c == implc -> anomaly "Implication must have 2 args" *)
    | App(c, Lam f, []) when c == pic ->
       run (depth+1) p f gs next alts lvl
    | App(c, Lam f, []) when c == sigmac ->
       let v = UVar(oref dummy, depth, 0) in
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
    | Custom(c, args) ->
       let f = try lookup_custom c with Not_found -> anomaly"no such custom" in
       let b = try Some (f depth [||] p args) with No_clause -> None in
       (match b with
          Some gs' ->
           (match List.map (fun g -> depth,p,g) gs' @ gs with
           | [] -> TCALL pop_andl alts next lvl
           | (depth,p,g) :: gs -> run depth p g gs next alts lvl)
        | None -> TCALL next_alt alts)

  and backchain depth p g gs cp next alts lvl =
    let maybe_last_call = alts == emptyalts in
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
        last_call := maybe_last_call && cs = [];
        let env = Array.make c.vars dummy in
        match
         for_all2 (unif depth env c.depth) args_of_g c.args
        with
        | false -> undo_trail old_trail; TCALL select cs
        | true ->
           let oldalts = alts in
           let alts = if cs = [] then alts else
             { program = p; depth = depth; goal = g; goals = gs; stack = next;
               trail = old_trail; clauses = cs; lvl = lvl ; next = alts} in
           begin match c.hyps with
           | [] ->
              begin match gs with
              | [] -> TCALL pop_andl alts next lvl
              | (depth,p,g)::gs -> TCALL run depth p g gs next alts lvl end
           | h::hs ->
              let next = if gs = [] then next else FCons (lvl,gs,next) in
              let h =
                to_heap depth ~from:c.depth ~to_:depth env h in
              let hs =
                List.map (fun x->
                  depth,p,
                  to_heap depth ~from:c.depth ~to_:depth env x)
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
    | [] -> pop_andl alts next lvl
    | (depth, p, g) :: gs -> run depth p g gs next alts lvl

  and pop_andl alts next lvl =
   match next with
    | FNil ->
        (match resume_all () with
           None ->
            Format.fprintf Format.std_formatter
             "Undo triggered by goal resumption\n%!";
            TCALL next_alt alts
         | Some ((ndepth,p,ng)::goals) ->
            run ndepth p ng goals FNil alts lvl
         | Some [] ->
            Format.fprintf Format.std_formatter "===================\n%!";
            print_delayed ();
            Format.fprintf Format.std_formatter "===================\n%!";
            alts)
    | FCons (_,[],_) -> anomaly "empty stack frame"
    | FCons(lvl,(depth,p,g)::gs,next) -> run depth p g gs next alts lvl

  and resume_all () =
   let ok = ref true in
   let to_be_resumed = ref [] in
   (* Phase 1: we analyze the goals to be resumed *)
   while !ok && !to_resume <> [] do
     match !to_resume with
     | (Delayed_unif (ad,e,bd,a,b), vars) as exn :: rest ->
         remove_constraint exn;
         to_resume := rest;
         Format.fprintf Format.std_formatter
          "Resuming @[<hov 2>^%d:%a@ == ^%d:%a@]\n%!"
           ad (uppterm ad [] 0 [||]) a
           bd (uppterm ad [] ad e) b;
         ok := unif ad e bd a b
     | (Delayed_goal((depth,_,_,g) as dpg), _) as exn :: rest ->
         remove_constraint exn;
         to_resume := rest;
         Format.fprintf Format.std_formatter
          "Resuming goal: ... ⊢ %a\n%!" (uppterm depth [] 0 [||]) g ;
         to_be_resumed := dpg :: !to_be_resumed
     | _ -> anomaly "Unknown constraint type"
   done ;
   (* Phase 2: we propagate the constraints *)
   (*if !new_delayed <> [] then Format.fprintf Format.std_formatter "RESUME ALL\n%!";*)
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
                  Format.fprintf Format.std_formatter
                   "Killing goal: ... ⊢ %a\n%!" (uppterm depth [] 0 [||]) g
              | _ -> ()) to_be_removed ;*)
             List.iter remove_constraint to_be_removed ;
             (*List.iter (fun (depth,_,_,g) ->
                  Format.fprintf Format.std_formatter
                   "Additional goal: ... ⊢ %a\n%!" (uppterm depth [] 0 [||]) g)
               to_be_added ;*)
             (*List.iter add_constraint to_be_added*)
             to_be_resumed := to_be_added @ !to_be_resumed )
     | _ -> anomaly "Empty list"
    done;
    Some (List.map (fun (d,p,_,g) -> d,p,g) (List.rev !to_be_resumed))
   end
   else None

  and next_alt alts =
   if alts == emptyalts then raise No_clause
   else
    let { program = p; clauses = clauses; goal = g; goals = gs; stack = next;
          trail = old_trail; depth = depth; lvl = lvl; next = alts} = alts in
    undo_trail old_trail;
    backchain depth p g gs clauses next alts lvl
  in


 (* Finally the runtime *)
 fun () ->
  let { Fork.exec = exec ; get = get ; set = set } = Fork.fork () in
  (fun ?(depth=0) p (_,argsdepth,q_env,q) ->
     set original_program p;
     exec (fun lcs ->
     let q = to_heap argsdepth ~from:depth ~to_:depth q_env q in
     run lcs p q [] FNil emptyalts emptyalts)),
  (fun alts -> exec next_alt alts),
  (fun () -> get delayed = [])
;;

do_make_runtime := make_runtime;;

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
  | AST.App (AST.String _,_) -> type_error "Applied string value"
  | AST.App (AST.Int _,_) -> type_error "Applied integer value"
  | AST.App (AST.Float _,_) -> type_error "Applied float value"
;;

(* BUG: I pass the empty amap, that is plainly wrong.
   Therefore the function only works on meta-closed terms. *)
let term_of_ast ~depth t =
 let argsdepth = depth in
 let freevars = mkinterval 0 depth 0 in
 let cmap =
  List.fold_left (fun cmap i ->
   ConstMap.add (Parser.ASTFuncS.from_string (string_of_constant i))
    (constant_of_dbl i) cmap
   ) ConstMap.empty freevars in
 let { max_arg = max; name2arg = l }, t =
  stack_term_of_ast depth empty_amap cmap t in
 let env = Array.make max dummy in
 to_heap argsdepth ~from:depth ~to_:depth ~avoid:def_avoid env t
;;

let query_of_ast_cmap lcs cmap t =
  let { max_arg = max; name2arg = l }, t =
    stack_term_of_ast lcs empty_amap cmap t in
  List.rev_map fst l, 0, Array.make max dummy, t
;;

let query_of_ast (lcs,_) t = query_of_ast_cmap lcs ConstMap.empty t;;

let program_of_ast (p : Parser.decl list) : program =
 let rec aux lcs clauses =
  let clauses,lcs,_,cmapstack as res =
   List.fold_left
    (fun (clauses,lcs,cmap,cmapstack) d ->
      match d with
         Parser.Clause t ->
          let names,_,env,t = query_of_ast_cmap lcs cmap t in
          (* Format.eprintf "%a\n%!" (uppterm 0 names 0 env) t ; *)
          let moreclauses, morelcs = clausify (Array.length env) lcs [] [] 0 t in
          List.rev_append moreclauses clauses, lcs+morelcs, cmap, cmapstack
       | Parser.Begin -> clauses, lcs, cmap, cmap::cmapstack
       | Parser.Accumulated p ->
          let moreclausesrev,lcs = aux lcs p in
           moreclausesrev@clauses, lcs, cmap, cmapstack
       | Parser.End ->
          (match cmapstack with
              [] ->
               (* TODO: raise it in the parser *)
               error "End without a Begin"
            | cmap::cmapstack -> clauses, lcs, cmap, cmapstack)
       | Parser.Local v ->
          clauses,lcs+1, ConstMap.add v (constant_of_dbl lcs) cmap, cmapstack
    ) ([],lcs,ConstMap.empty,[]) clauses in
  if cmapstack <> [] then error "Begin without an End" else clauses,lcs in
 let clausesrev,lcs = aux 0 p in
  lcs,make_index (List.rev clausesrev)
;;

(*let pp_FOprolog p = assert false (*CSC: port the code, see function above List.iter (fun { Parser.head = a; hyps = f } ->
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
;;*)


let rec pp_FOprolog p = 
 List.iter
  (function
      Parser.Local _
    | Parser.Begin
    | Parser.End -> assert false (* TODO *)
    | Parser.Accumulated l -> pp_FOprolog l
    | Parser.Clause t ->
       (* BUG: ConstMap.empty because "local" declarations are ignored ATM *)
       let names,_,env,t = query_of_ast_cmap 0 ConstMap.empty t in
       match t with
       | App(_, Custom _, _) | App(_,_,(Custom _)::_) -> ()  
       | App(hd,a,[f]) when hd == rimplc -> 
         Format.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
          (prologppterm names env) a
          (pplist (prologppterm names env) ",") (split_conj f);
       | _ -> 
         Format.eprintf "@[<hov 1>%a.@]\n%!" (prologppterm names env) t 
  ) p  
 ;;

 
(* RUN with non indexed engine *)
type query = string list * int * term array * term
let pp_prolog = pp_FOprolog

let execute_once (depth,p) q =
 let run, cont, _ = make_runtime () in
 try ignore (run p q depth) ; false
 with No_clause -> true
;;

let execute_loop (depth,p) ((q_names,q_argsdepth,q_env,q) as qq) =
 let run, cont, _ = make_runtime () in
 let k = ref emptyalts in
 let do_with_infos f x =
  let time0 = Unix.gettimeofday() in
  f x ;
  let time1 = Unix.gettimeofday() in
  prerr_endline ("Execution time: "^string_of_float(time1 -. time0));
 (* Format.eprintf "Raw Result: %a\n%!" (ppterm depth q_names q_argsdepth q_env) q ;*)
  Format.eprintf "Result: \n%!" ;
  List.iteri (fun i name -> Format.eprintf "@[<hov 1>%s=%a@]\n%!" name
   (uppterm depth q_names 0 q_env) q_env.(i)) q_names in
 do_with_infos (fun _ -> k := (run p qq depth)) ();
 while !k != emptyalts do
   prerr_endline "More? (Y/n)";
   if read_line() = "n" then k := emptyalts else
    try do_with_infos (fun _ -> k := cont !k) ()
    with No_clause -> prerr_endline "Fail"; k := emptyalts
 done
;;

(* }}} *)

(* vim: set foldmethod=marker: *)
