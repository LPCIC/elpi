
(* A map with opaque bodex data as key.

This data structure is faster than an associative list + List.assq
asyntotically since it keeps a cache with log(n) lookup time.

On standard OCaml backends we compuete the pointer of a boxed value and
turn it into an integer key and use that value as the key for the cache.
Since the Gc may move the boxed value a sanity check is performed at lookup
time and the cache is eventually updated on the bases of an authoritative
associative list.    
*)
module IntMap = Map.Make(struct type t = int let compare = Stdlib.compare end)
module PtrMap : sig

  type 'a t

  val empty : unit -> 'a t
  val is_empty : 'a t -> bool
  val find : 'block -> 'a t -> 'a
  val add : 'block -> 'a -> 'a t -> 'a t
  val remove : 'block -> 'a t -> 'a t
  val filter : ('block -> 'a -> bool) -> 'a t -> 'a t
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

  val intersect : 'a t -> 'a t -> bool

end = struct

  type 'a t = {
    (* maps the key's address to the value. It also holds the key
       itself so that we can check if the key was moved by the Gc
       and fall back to the authoritative associative list *)
    mutable cache : (Obj.t * 'a) IntMap.t;
    (* We associate to the boxed key a value, but we also keep track of
       its address. When it is found to be outdated, we remove the old
       entry in the cache. All OCaml data is eventually moved by the Gc
       at least once, so we keep the size of the cache close to the
       size of the list, and not to its double, by puring outdated cache
       entries. *)
    authoritative : (Obj.t * ('a * int ref)) list;
  }

  let empty () = { cache = IntMap.empty; authoritative = [] }
  let is_empty { authoritative; _ } = authoritative = []

  let address_of =
    match Sys.backend_type with
    | (Sys.Bytecode | Sys.Native) ->
        fun (ro : Obj.t) : int -> begin
          assert(Obj.is_block ro);
          let a : int = Obj.magic ro in
          ~- a (* so that the Gc will not mistake it for a block *)
        end
    | Sys.Other _ ->
        (* We don't know how the backend deals with memory, so we play safe.
           In this way the cache is a 1 slot for the last used entry. *)
        fun _ -> 46

  let add o v { cache;  authoritative } =
    let ro = Obj.repr o in
    let address = address_of ro in
    { cache = IntMap.add address (ro,v) cache;
      authoritative = (ro,(v,ref address)) :: authoritative }

  let linear_search_and_cache ro address cache authoritative orig =
    let v, old_address = List.assq ro authoritative in
    orig.cache <- IntMap.add address (ro,v) (IntMap.remove !old_address cache);
    old_address := address;
    v

  let linear_scan_attempted = ref false
  let find o ({ cache; authoritative } as orig) =
    linear_scan_attempted := false;
    let ro = Obj.repr o in
    let address = address_of ro in
    try
      let ro', v = IntMap.find address cache in
      if ro' == ro then v
      else
        let cache = IntMap.remove address cache in
        linear_scan_attempted := true;
        linear_search_and_cache ro address cache authoritative orig        
    with Not_found when not !linear_scan_attempted -> 
      linear_search_and_cache ro address cache authoritative orig

  let mem o m =
    try
      let _ = find o m in
      true
    with Not_found -> false

  let intersect m { authoritative; _ } =
    authoritative |> List.exists (fun (o,_) -> mem o m)    

  let remove o { cache; authoritative } =
    let ro = Obj.repr o in
    let address = address_of ro in
    let _, old_address = List.assq ro authoritative in
    let authoritative = List.remove_assq ro authoritative in
    let cache = IntMap.remove address cache in
    let cache =
      if !old_address != address then IntMap.remove !old_address cache
      else cache in
    { cache; authoritative }

  let filter f { cache; authoritative } =
    let cache = ref cache in
    let authoritative = authoritative |> List.filter (fun (o,(v,old_address)) ->
      let keep = f (Obj.obj o) v in
      if not keep then begin
        let address = address_of o in
        cache := IntMap.remove address !cache;
        if !old_address != address then cache := IntMap.remove !old_address !cache
      end;
      keep) in
    { cache = !cache; authoritative }

  let pp f fmt { authoritative; _ } =
    Format.pp_print_list (fun fmt (_,(x,_)) -> f fmt x) ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ";") fmt authoritative

  let show f m = Format.asprintf "%a" (pp f) m
    
end

(******************************* ast ****************************)
open Ast
let dummy = App("!",[App("!",[])])
let cut = App("!",[])

let rid = ref 0 (* trace_ppx, runtime id *)

module Pp = struct

let pp_var, pp_reset =
  let l = ref [] in
  (fun v ->
    try
      List.assq v !l
    with Not_found ->
      let s = "X" ^ string_of_int (List.length !l) in
      l := (v,s) :: !l;
      s),
  (fun () -> l := [])

let rec pp fmt = function
  | App(c,[]) -> Format.fprintf fmt "%s" c
  | App(c,l) -> Format.fprintf fmt "@[<hov 2>%s(%a)@]" c (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp) l
  | Var r when !r <> dummy -> pp fmt !r
  | Var r -> let s = pp_var r in Format.fprintf fmt "%s" s
  | Arg i -> Format.fprintf fmt "$%d" i

let ppi fmt = function
  | App(s,[a;b]) -> pp fmt a; Format.fprintf fmt " %s " s; pp fmt b
  | _ -> assert false

let pp_tm = pp
let ppl s = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f s) pp
let ppli s = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f s) ppi

end
let pp_tm = Pp.pp

(******************************* backtrack ****************************)

module Heap = struct

type history_item =
  | Assign of tm ref * history
  | Restore of tm ref * tm * history
  | AddConstraint of tm * history
  | RmConstraint of tm * history
  | Top
and history = history_item ref
(*[@@deriving show { with_path = false }]*)
let pp_history fmt _ = Format.fprintf fmt "<history>"

type t = {
  log : history ref; (* tracks the tip *)
  constraints : tm list ref;
}
(*[@@deriving show { with_path = false }]*)
let pp fmt _ = Format.fprintf fmt "<heap>"

let assign { log = trail; _ }  v t =
  assert(! (!trail) = Top);
  let new_top = ref Top in
  !trail := Assign(v,new_top);
  trail := new_top;
  [%spy "assign" ~rid pp_tm (Var v)];
  [%spy "assign:with" ~rid pp_tm t];
  v := t

let add_cs { log = trail; constraints } c =
  let new_top = ref Top in
  !trail := AddConstraint(c,new_top);
  trail := new_top;
  constraints := !constraints @ [c]
  
let del_cs { log = trail; constraints } c =
  let new_top = ref Top in
  !trail := RmConstraint(c,new_top);
  trail := new_top;
  constraints := List.filter (fun x -> x != c) !constraints
  
let backtrack log cstore last_choice_point =
  let rec aux h k =
    match !h with
    | Top -> k ()
    | Assign(r,h') ->
        aux h' (fun () ->
          h' := Restore(r,!r, h);
          r := dummy;
          k ())
    | Restore(r,v,h') ->
        aux h' (fun () ->
          h' := Assign(r,h);
          r := v;
          k ())
    | AddConstraint(c,h') ->
        aux h' (fun () ->
          h := RmConstraint(c,h);
          cstore := List.filter (fun x -> x != c) !cstore;
          k ())
    | RmConstraint(c,h') ->
      aux h' (fun () ->
        h := AddConstraint(c,h);
        cstore := c :: !cstore;
        k ())
      in
    aux last_choice_point (fun () ->
      log := last_choice_point;
      last_choice_point := Top)

let backtrack (heap : t) (point : history) =
  backtrack heap.log heap.constraints point

let checkpoint (heap : t) : history = !(heap.log)

let init ~constraints =
  let top = ref Top in
  { log = ref top; constraints = ref constraints }

end

type goal = tm
[@@deriving show { with_path = false }]

type constraints = tm list
[@@deriving show { with_path = false }]

type rule = { hd : tm; nvars : int; csts : constraints; hyps : tm list }
[@@deriving show { with_path = false }]
type solution = rule (* with empty hyps *)
[@@deriving show { with_path = false }]

type rules = rule list
[@@deriving show { with_path = false }]

let pp_rule_hd fmt { hd; _ } = pp_tm fmt hd

(******************************* unif ****************************)

let rec fold_left2 f l1 l2 = match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> f x y && fold_left2 f xs ys
  | _ -> false

let rec predicate_of = function
  | App(c,_) -> c
  | Var r when !r != dummy -> predicate_of !r
  | _ -> assert false

let rec heapify s = function
  | App(c,l) -> App(c,List.map (heapify s) l)
  | Var _ as x -> x
  | Arg i when s.(i) != dummy -> s.(i)
  | Arg i -> let t = Var (ref dummy) in s.(i) <- t; t

let rec unif (trail:Heap.t) (sb:tm array) (a:tm) (b:tm) = match a, b with
  | Arg _, _ -> assert false

  (* deref *)
  | Var r, _ when !r != dummy -> unif trail sb !r b
  | _, Var r when !r != dummy -> unif trail sb a !r
  | _, Arg i when sb.(i) != dummy -> unif trail sb a sb.(i)

  (* assign *)
  | _, Arg i -> sb.(i) <- a; true
  | Var r, _ -> Heap.assign trail r (heapify sb b); true
  | _, Var r -> Heap.assign trail r a; true (* missing OC *)

  | App(c1,args1), App(c2,args2) ->
    if c1 <> c2 then false
    else fold_left2 (unif trail sb) args1 args2

(******************************* table ****************************)

type canonical_goal = tm
[@@deriving show { with_path = false }]

type varmap = int * int PtrMap.t

let abstract ?(from : varmap option) (g : goal) : varmap * canonical_goal =
  let i, m = match from with None -> 0, PtrMap.empty () | Some(i,m) -> i, m in
  let i = ref i in
  let m = ref m in
  let rec aux = function
    | Arg _ -> assert false
    | Var r when !r <> dummy -> aux !r
    | Var r ->
        begin match PtrMap.find r !m with
        | n -> Arg(n)
        | exception Not_found when from = None ->
            m := PtrMap.add r !i !m;
            let x = Arg !i in
            incr i;
            x
        | exception Not_found -> (* used when abstracting constraints, this variable is not in the head of the clause *)
            Var r
        end
    | App(s,args) ->
        let args = List.map aux args in
        App(s,args)
  in
  let abstract = aux g in
  (!i, !m), abstract
    
let abstract_constraints (from : varmap) constraints : int * constraints =
  let rec aux from relevant irrelevant changed = function
    | [] -> changed, from, relevant, irrelevant
    | (((_,f1),_),c as x) :: rest ->
        if PtrMap.intersect (snd from) f1 then
          let from, c = abstract ~from c in
          aux from (c :: relevant) irrelevant true rest
        else
          aux from relevant (x :: irrelevant) changed rest
  in
  let rec fixpoint from relevant csts =
    let changed, from, relevant, irrelevant = aux from relevant [] false csts in
    if changed then fixpoint from relevant irrelevant
    else fst from, relevant
  in
  let constraints = List.map (fun c -> abstract c, c) constraints in
  fixpoint from [] constraints

module DT : sig
    
    type 'a t
    val empty : 'a t
    val add : canonical_goal -> 'a -> 'a t -> 'a t
    val mem : canonical_goal -> 'a t -> bool
    val find : canonical_goal -> 'a t -> 'a
    val remove : canonical_goal -> 'a t -> 'a t
    type path
    val pp_path : Format.formatter -> path -> unit
    val iter : (path -> 'a -> unit) -> 'a t -> unit
    val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

end = struct
    
    type path_string_elem = string * int
    type path = path_string_elem list
    let rec path_string_of = function
      | Arg i -> ["$"^string_of_int i, 0]
      | Var r when !r <> dummy -> assert false
      | Var _ -> assert false (* we are on canonical goals *)
      | App(s,args) ->
          let arity = List.length args in
          (s,arity) ::
            List.flatten (List.map path_string_of args)

  module OrderedPathStringElement = struct
    type t = path_string_elem
    let compare = Stdlib.compare
  end
  module PSMap = Map.Make(OrderedPathStringElement);;
  module Trie = Trie.Make(PSMap);;
  include Trie

  let mem i t = mem (path_string_of i) t
  let add i v t = add (path_string_of i) v t
  let find i t = find (path_string_of i) t

  let remove i t = remove (path_string_of i) t
  let iter f t = iter f t

  let pp_path fmt p =
    let pp_comma n = if n > 1 then Format.fprintf fmt ", " else () in
    let rec aux n = if n = 0 then fun x -> x else function
      | (s,0) :: rest -> Format.fprintf fmt "%s" s; pp_comma n; aux (n-1) rest
      | (s,m) :: rest -> Format.fprintf fmt "%s(" s; let rest = aux m rest in Format.fprintf fmt ")"; pp_comma n; aux (n-1) rest
      | [] -> []
  in
    let _ = aux 1 p in
    ()

  let pp f fmt t =
    let p k v = Format.fprintf fmt "@[<hov 2>%a |->@ %a@]@ " pp_path k f v in
    Format.fprintf fmt "@[<hov>";
    iter p t;
    Format.fprintf fmt "@]"

end

(******************************* run ****************************)

type continuation = (* the AND part, what to do next *)
  | Done (* Program end *)
  | SolveGoals of {
      brothers : goal list;
      cut_alts : alt; [@printer (fun _ _ -> ())] (* in elpi this is kept by passing it to run for the immediate brothers *)
      next : continuation;
    }
  | ExitSLGRoot of { heap : Heap.t; [@printer (fun _ _ -> ())] next : continuation; alts : alt }
  | TableSolution of { entry : canonical_goal; solution : tm }

and alt = (* the OR part, what to do if we fail *)
  | NoAlt
  | ExploreAnotherSLDPath of {
    goal: goal;
    rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
    next : continuation;
    alts : alt;
    choice_point : Heap.history;
   }
  | UnblockSLGGenerator of { generator : slg_generator; alts : alt } (* a ! did not fire *)

and slg_generator =
  | Root of {
      initial_goal : slg_initial_goal;
      rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
    }
  | UnexploredBranches of { heap : Heap.t; alts : alt }

and slg_initial_goal = {
  nvars : int;
  cgoal : canonical_goal;
  ccsts : constraints; (* canonical as well *)
}
[@@deriving show { with_path = false }]

let ifanyrule = function
  | ExploreAnotherSLDPath { rules; alts; _ } as x ->
      if rules = [] then alts else x
  | x -> x

let ifanygoals = function
  | SolveGoals { brothers = []; next; _ } -> next
  | x -> x

let rec flatten_frame = function
  | SolveGoals { brothers; next; _ } ->
      let goals, action = flatten_frame next in
      brothers @ goals, action
  | x -> [], x

let pp_end_frame fmt = function
  | Done -> Format.fprintf fmt "Done"
  | ExitSLGRoot _ -> Format.fprintf fmt "ExitSLGRoot"
  | TableSolution { entry = cg; solution } -> Format.fprintf fmt "TableSolution %a to %a" pp_tm solution pp_tm cg
  | _ -> assert false

let _pp_continuation fmt continuation =
  let brothers, siblings = flatten_frame continuation in
    Format.fprintf fmt "%a; %a"
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f "; ") pp_tm) brothers
      pp_end_frame siblings

(* the program *)  
let all_rules = ref []
let gas = ref 0

let tabled = function
  | App(s,_) -> s.[0] = '_'
  | _ -> false

type table_entry_status = Incomplete | Complete
[@@deriving show { with_path = false }]

let table = ref DT.empty

let pp_table fmt dt =
 DT.iter (fun k (l,s) -> Format.fprintf fmt "%a -> (%a, [%a])@ "
     DT.pp_path k
     pp_table_entry_status s (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ") pp_rule_hd) l) dt

let table_reset () = table := DT.empty

let csts_consistent _ _ = true (* consistency of constraint store *)

let rec select (heap : Heap.t) goal = function
  | [] -> [%spy "select:no-rule" ~rid Format.pp_force_newline ()]; None
  | { nvars; hd; csts ; hyps } ::rules ->
    let stack = Array.init nvars (fun _ -> dummy) in
    let prev = Heap.checkpoint heap in
    if not (unif heap stack goal hd) then begin
      [%spy "select:rule-ko" ~rid (fun fmt () ->
        let pp_csts fmt csts =
          if csts = [] then () else pp_tm fmt (App("|",csts)) in
        let pp_hyps fmt hyps =
          if hyps = [] then () else Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_tm fmt hyps in
        Format.fprintf fmt "@[<hov 2>%a :-@ %a@ %a@]." pp_tm hd pp_csts csts pp_hyps hyps) ()];
      Heap.backtrack heap prev;
      select heap goal rules
    end else begin
      [%spy "select:rule-ok" ~rid (fun fmt () ->
          let pp_csts fmt csts =
            if csts = [] then () else pp_tm fmt (App("|",csts)) in
          let pp_hyps fmt hyps =
            if hyps = [] then () else Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_tm fmt hyps in
          Format.fprintf fmt "@[<hov 2>%a :-@ %a@ %a@]." pp_tm hd pp_csts csts pp_hyps hyps) ()];
      let csts = List.map (heapify stack) csts in
      if csts_consistent csts !(heap.constraints) then begin
        List.iter (Heap.add_cs heap) csts;
        Some (prev, List.map (heapify stack) hyps, rules)
      end else begin
        Heap.backtrack heap prev;
        select heap goal rules
      end
    end
let select h goal r =
  [%spy "select:goal" ~rid pp_tm goal];
  select h goal r

let filter g rules =
  let p = predicate_of g in
  let rules = List.filter (fun { hd; _ } -> predicate_of hd = p) rules in
  rules

let new_table_entry cgoal =
  table := DT.add cgoal ([],Incomplete) !table

type slg_consumer = {
  goal : goal;
  next : continuation;
  heap : Heap.t;
  checkpoint : Heap.history;
}
[@@deriving show { with_path = false }]

let init_tree { nvars = stack; cgoal = cg; ccsts = cs } =
  let stack = Array.init stack (fun _ -> dummy) in
  let g = heapify stack cg in
  let cs = List.map (heapify stack) cs in
  cg, g, Heap.init ~constraints:cs

type slg_status = {
  generators : slg_generator list;
  consumers : slg_consumer list DT.t;
  resume_queue : (slg_consumer * solution) list;
  root : (canonical_goal * (Heap.t * alt) option) option;
}
[@@deriving show { with_path = false }]

let empty_slg_status = {
  consumers = DT.empty;
  generators = [];
  resume_queue = [];
  root = None;
}

type sld_status = {
  goal : goal;
  next : continuation;
  heap : Heap.t;
  cut_alts : alt;
  rules : rule list; (* either the program or the tables solutions *)
  alts : alt;
}

let dt_append k v t =
  try
    let old = DT.find k t in
    DT.add k (old @ [v]) t
  with Not_found ->
    DT.add k [v] t
   
    
let push_consumer cgoal (c : slg_consumer) (s : slg_status) =
  { s with consumers = dt_append cgoal c s.consumers }

let push_generator (g : slg_generator) (s : slg_status) =
  { s with generators = g :: s.generators }

let set_root_if_not_set cgoal heap alts s : slg_status =
  if s.root = None then { s with root = Some(cgoal, Some(heap, alts)) } else s

let resume_all_consumers cgoal (c : solution) (s : slg_status) =
  try
    let consumers = DT.find cgoal s.consumers in
    {s with resume_queue = List.map (fun x -> x,c) consumers @ s.resume_queue }
  with Not_found -> (* consumers may have been cut away *)
    s
  
let table_solution cgoal solution constraints (s : slg_status) : slg_status * bool =
  match DT.find cgoal !table with
  | solutions, status ->
      let abstract_map, hd = abstract solution in
      let nvars, csts = abstract_constraints abstract_map constraints in
      let solution = { hyps = []; nvars; hd; csts } in
      if List.mem solution solutions then
        s, false
      else begin
        table := DT.add cgoal (solutions @ [solution], status) !table;
        resume_all_consumers cgoal solution s, true
      end
  | exception Not_found -> assert false
    
let table_entry_complete cgoal sgs =
  match DT.find cgoal !table with
  | solutions, Incomplete ->
      table := DT.add cgoal (solutions, Complete) !table;
      let sgs = { sgs with consumers = DT.remove cgoal sgs.consumers } in
      sgs
  | _, Complete -> sgs (* entry may have been completed early by a cut *)
  | exception Not_found -> assert false

let table_last_solution cgoal solution constraints s =
  let s, progress = table_solution cgoal solution constraints s in
  table_entry_complete cgoal s, progress
  

let is_root_complete root_entry =
 match root_entry with
 | None -> true
 | Some (cgoal,_) ->
     match DT.find cgoal !table with
     | _, Complete -> true
     | _, Incomplete -> false
     | exception Not_found -> assert false

let has_cut = List.mem cut

type result = TIMEOUT | FAIL | OK of tm list * Heap.t * alt * slg_status

module type Runtime = sig

  val run : canonical_goal list -> rule list -> result
  val next_alt : Heap.t -> alt -> slg_status -> result

end


module SLD : Runtime = struct

  (* called on a goal as we see it for the first time *)
let rec run { goal; rules; next; alts; cut_alts; heap } (sgs : slg_status) : result =
  [%trace "run" ~rid 
    ("@[<v>goal = %a@ next = %a@ alts = %a@]@\n" pp_tm goal pp_continuation next pp_alt alts)
  begin 
    let rules = filter goal rules in
    sld goal rules next alts cut_alts heap sgs
end]

and sld goal rules next (alts : alt) (cut_alts : alt) (heap: Heap.t) (sgs : slg_status) =
  if !gas = 0 then TIMEOUT else let () = decr gas in
  if goal = cut then
    pop_andl next cut_alts heap sgs
  else 
    match select heap goal rules with
    | None -> next_alt heap alts sgs
    | Some (choice_point, [], rules) ->
        let alts = ifanyrule @@ ExploreAnotherSLDPath { goal; rules; next; choice_point; alts } in
        pop_andl next alts heap sgs
    | Some (choice_point, ngoal :: brothers, rules) ->
        let old_alts = alts in
        let alts = ifanyrule @@ ExploreAnotherSLDPath { goal; rules; next; choice_point; alts } in
        let next = ifanygoals @@ SolveGoals { brothers; cut_alts = old_alts; next } in
        run { goal = ngoal; rules = !all_rules; next; alts; cut_alts = old_alts; heap } sgs

and pop_andl (next : continuation) (alts : alt) (heap : Heap.t) (sgs : slg_status) =
  [%trace "pop_andl" ~rid ("@[<hov 2>next = %a@]\n" pp_continuation next) begin
  match next with
  | Done -> OK (!(heap.constraints),heap,alts,sgs)
  | SolveGoals { brothers = []; next; _ } -> pop_andl next alts heap sgs
  | SolveGoals { brothers = goal :: brothers; cut_alts; next } ->
    run { goal; rules = !all_rules;
    next = SolveGoals { brothers = brothers; cut_alts; next };
    alts; cut_alts; heap; } sgs
  | ExitSLGRoot _ -> assert false
  | TableSolution _ -> assert false
  end]

and next_alt (heap : Heap.t) (alts : alt) (sgs : slg_status) : result =
  [%trace "next_alt" ~rid ("@[<hov 2>%a]@\n" pp_alt alts) begin
  match alts with
  | NoAlt -> FAIL
  | UnblockSLGGenerator _ -> assert false
  | ExploreAnotherSLDPath { goal; rules; next; choice_point ; alts } ->
      Heap.backtrack heap choice_point;
      sld goal rules next (alts : alt) (NoAlt : alt) (heap: Heap.t) (sgs : slg_status)
  end]

let run goal rules =
  let heap = Heap.init ~constraints:[] in
  let slg_status = empty_slg_status in
  let sld_status =
    match goal with
    | [] -> assert false
    | [goal] -> { goal; rules; next = Done; alts = NoAlt; cut_alts = NoAlt; heap }
    | goal::gs -> { goal; rules; next = ifanygoals @@ SolveGoals { brothers = gs; next = Done; cut_alts = NoAlt }; alts = NoAlt; cut_alts = NoAlt; heap }
  in
  run sld_status slg_status

end

module SLG : Runtime = struct

(* called on a goal as we see it for the first time *)
let rec run { goal; rules; next; alts; cut_alts; heap } (sgs : slg_status) : result =
  [%trace "run" ~rid 
  ("@[<v>goal = %a@ next = %a@ alts = %a@]@\n" pp_tm goal pp_continuation next pp_alt alts)
  begin
    let rules = filter goal rules in
    if tabled goal
    then enter_slg goal rules next alts cut_alts heap sgs
    else       sld goal rules next alts cut_alts heap sgs
end]

and enter_slg goal rules next alts cut_alts heap sgs =
  let abstract_map, cgoal = abstract goal in
  match DT.find cgoal !table with
  | [], Incomplete ->
      [%spy "slg:suspend" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; heap; checkpoint = Heap.checkpoint heap } sgs in
      slg sgs
  | answers, Complete -> (* TODO: Trie -> DT(find_unifiable) *)
      [%spy "slg:complete->sld" ~rid pp_tm cgoal];
      sld goal answers next alts cut_alts heap sgs
  | answers, Incomplete ->
      [%spy "slg:incomplete->sld+slg" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; heap; checkpoint = Heap.checkpoint heap } sgs in
      sld goal answers next alts cut_alts heap sgs
  | exception Not_found ->
      [%spy "slg:new" ~rid pp_tm cgoal];
      let sgs = set_root_if_not_set cgoal heap alts sgs in
      let sgs = push_consumer cgoal { goal; next = ExitSLGRoot { heap; next; alts }; heap; checkpoint = Heap.checkpoint heap } sgs in
      new_table_entry cgoal;
      let nvars, ccsts = abstract_constraints abstract_map !(heap.constraints) in
      let sgs = push_generator (Root { initial_goal = { nvars ; cgoal ; ccsts }; rules }) sgs in
      slg sgs

and slg ({ generators; resume_queue; root; _ } as s) =
  if !gas = 0 then TIMEOUT else let () = decr gas in
  [%trace "slg:step" ~rid ("@[<hov 2>%a@ table: @[<hv>%a@]@]\n" pp_slg_status s pp_table !table)
  begin match resume_queue with
  | ({ goal; next; heap; checkpoint }, solution) :: resume_queue ->
      [%spy "slg:resume" ~rid];
      let s = { s with resume_queue } in
      Heap.backtrack heap checkpoint;
      begin match select heap goal [solution] with
      | None -> slg s
      | Some(_,[],[]) -> pop_andl next NoAlt heap s (* #1 *)
      | _ -> assert false (* solutions have no subgoals *)
      end
  | [] ->
     if (*is_root_complete root ||*) generators = [] then (* Hum, we should do a SCC here, there is not necessarily ONE root *)
       match root with
       | None -> FAIL (* if no sld alts, then we always try slg *)
       | Some (_,None) -> FAIL (* no slg alts and no generators *)
       | Some (e,Some(heap,alts)) -> next_alt heap alts { s with root = Some (e,None) }
     else
     let () = [%spy "slg:generator" ~rid] in 
     match generators with
     | [] -> assert false
     | UnexploredBranches { alts = NoAlt; _ } :: _ -> assert false
     | UnexploredBranches { heap; alts } :: generators ->
        let s = { s with generators } in
        next_alt heap alts s
     | Root { initial_goal = { cgoal = entry; _ }; rules = []; _ } :: generators ->
        let s = { s with generators } in
        let s = table_entry_complete entry s in
        [%spy "slg:completed" ~rid pp_tm entry];
        slg s
     | Root { initial_goal; rules } :: generators ->
        let s = { s with generators } in
        let entry, goal, heap = init_tree initial_goal in
        match select heap goal rules with
        | None ->
            let s = table_entry_complete entry s in
            [%spy "slg:completed" ~rid pp_tm entry];
            slg s
        | Some (_,subgoals, rules) ->
            let generator = Root { initial_goal; rules } in
            match subgoals with
            | [] ->
                let s = push_generator generator s in
                pop_andl (TableSolution { entry; solution = goal}) NoAlt heap s
            | ngoal :: brothers ->
                let next = ifanygoals @@ SolveGoals { brothers; cut_alts = NoAlt; next = TableSolution { entry; solution = goal } } in
                if has_cut subgoals then
                  let alts = UnblockSLGGenerator { generator; alts = NoAlt } in (* this is cut away if the subgoal ! is reached *)
                  run { goal = ngoal; next; alts; rules = !all_rules; cut_alts = NoAlt; heap; } s        
                else
                  let s = push_generator generator s in
                  run { goal = ngoal; next; alts = NoAlt; rules = !all_rules; cut_alts = NoAlt; heap } s        
end]

and sld goal rules next (alts : alt) (cut_alts : alt) (heap: Heap.t) (sgs : slg_status) =
  if !gas = 0 then TIMEOUT else let () = decr gas in
  if goal = cut then
    pop_andl_maybe_tabled_tail_cut next cut_alts heap sgs
  else 
    match select heap goal (filter goal rules) with
    | None -> next_alt heap alts sgs
    | Some (choice_point, [], rules) ->
        let alts = ifanyrule @@ ExploreAnotherSLDPath { goal; rules; next; choice_point; alts } in
        pop_andl next alts heap sgs
    | Some (choice_point, ngoal :: brothers, rules) ->
        let old_alts = alts in
        let alts = ifanyrule @@ ExploreAnotherSLDPath { goal; rules; next; choice_point; alts } in
        let next = ifanygoals @@ SolveGoals { brothers; cut_alts = old_alts; next } in
        run { goal = ngoal; rules = !all_rules; next; alts; cut_alts = old_alts; heap } sgs

and pop_andl_maybe_tabled_tail_cut next alts heap sgs =
  match next with
  | SolveGoals { brothers = []; next; _ } -> pop_andl_maybe_tabled_tail_cut next alts heap sgs
  | TableSolution { entry; solution } ->
      let sgs, progress = table_last_solution entry solution !(heap.constraints) sgs in
      if progress then
        slg sgs
      else
        next_alt heap alts sgs
| x -> pop_andl x alts heap sgs

and pop_andl (next : continuation) (alts : alt) (heap : Heap.t) (sgs : slg_status) =
  [%trace "pop_andl" ~rid ("@[<hov 2>next = %a@]@\n" pp_continuation next) begin
  match next with
  | Done -> OK (!(heap.constraints),heap,alts,sgs)
  | SolveGoals { brothers = []; next; _ } -> pop_andl next alts heap sgs
  | SolveGoals { brothers = goal :: brothers; cut_alts; next } ->
      run { goal; rules = !all_rules;
            next = ifanygoals @@ SolveGoals { brothers = brothers; cut_alts; next };
            alts; cut_alts; heap; } sgs
  | ExitSLGRoot { heap; next; alts = o } -> assert(alts = NoAlt (* #1 *)); pop_andl next o heap sgs
  | TableSolution { entry; solution } ->
      let sgs, progress = table_solution entry solution !(heap.constraints) sgs in
      if progress then
        let sgs = if alts = NoAlt then sgs else push_generator (UnexploredBranches { heap; alts }) sgs in
        slg sgs
      else
        next_alt heap alts sgs
          
  end]

and next_alt (heap : Heap.t) (alts : alt) (sgs : slg_status) : result =
  [%trace "next_alt" ~rid ("@[<hov 2>%a]@\n" pp_alt alts) begin
  match alts with
  | NoAlt -> slg sgs
  | UnblockSLGGenerator { generator ; alts } ->
      let sgs = push_generator generator sgs in
      next_alt heap alts sgs
  | ExploreAnotherSLDPath { goal; rules; next; choice_point ; alts } ->
      Heap.backtrack heap choice_point;
      sld goal rules next (alts : alt) (NoAlt : alt) (heap: Heap.t) (sgs : slg_status)
  end]

let run goal rules =
  let heap = Heap.init ~constraints:[] in
  let slg_status = empty_slg_status in
  let sld_status =
    match goal with
    | [] -> assert false
    | [goal] -> { goal; rules; next = Done; alts = NoAlt; cut_alts = NoAlt; heap }
    | goal::gs -> { goal; rules; next = ifanygoals @@ SolveGoals { brothers = gs; next = Done; cut_alts = NoAlt }; alts = NoAlt; cut_alts = NoAlt; heap }
  in
  run sld_status slg_status

end

(***************************** TEST *************************)
module P = struct

  let l = ref []


  let v s =
    begin match s.[0] with
    | 'A'..'Z' -> 
        begin try
          let i = List.assoc s !l in
          Arg i
        with Not_found ->
          l := (s, List.length !l) :: !l;
          Arg (List.assoc s !l)
        end
    | _ -> App(s,[])
    end

  let cvars (s1,s2) = App("<",[v s1; v s2])

  let rec vars = function
    | App(s,[]) -> v s
    | App(x,xs) -> App(x,List.map vars xs)
    | x -> x
  

  let parse_program s = try
    let lexbuf = Lexing.from_string s in
    let cl = Parser.program Lexer.token lexbuf in
    cl |> List.map (fun (hd,csts,hyps) ->
        l := [];
        let hd = vars hd in
        let hyps = List.map vars hyps in
        let csts = List.map cvars csts in
        { nvars = List.length !l ; hd ; csts ; hyps })
    with Parser.Error -> Format.eprintf "cannot parse %s\n%!" s; exit 1

  let parse_query s = try
    l := [];
    let lexbuf = Lexing.from_string s in
    let goals = Parser.query Lexer.token lexbuf in
    let goals = List.map vars goals in
    let stack = Array.init (List.length !l) (fun _ -> dummy) in
    let goals = List.map (heapify stack) goals in
    goals
  with Parser.Error -> Format.eprintf "cannot parse %s\n%!" s; exit 1

end

let main query steps n program =
  (* let module R = SLD in *)
  let module R = SLG in
  let program = P.parse_program program in
  let query = P.parse_query query in
  all_rules := program;
  gas := steps;
  Pp.pp_reset ();
  table_reset ();
  let rec all n = function
  | FAIL -> [Format.asprintf "no"]
  | TIMEOUT -> [Format.asprintf "steps"]
  | OK (csts,heap,alts,sgs) ->
      let g = Format.asprintf "%a" (Pp.ppl ", ") query in
      let c = if csts = [] then "" else Format.asprintf "%a| " (Pp.ppli ", ") csts in
      let s = c^g in
      [%spy "solution" ~rid (fun x -> Format.fprintf x "%s\n\n") s];
      if n = 1 then [s]
      else s :: all (n-1) (R.next_alt heap alts sgs)
  in
  all n (R.run query !all_rules)

let errors = ref 0
let check ?(steps=1000) (`Check(s,p,q,l1)) =
  let l2 = main q steps (List.length l1) p in
  if l1 <> l2 then begin
    incr errors;
    Format.eprintf "\nERROR: %s\nExpected: %a\nActual:   %a\n%!" s
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l1
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l2
  end else
    Format.eprintf "@[<hov 2>   %s: ok (%d steps)@]\n%!" s (steps - !gas)
    (*Format.eprintf "@[<hov 2> %s: ok (%d steps, table: @[<hov>%a@])@]\n%!" s (steps - !gas) pp_table !table*)

