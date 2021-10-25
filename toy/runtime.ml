
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

(******************************* backtrack ****************************)

type history_item =
  | Assign of tm ref * history
  | Restore of tm ref * tm * history
  | AddConstraint of tm * history
  | RmConstraint of tm * history
  | Top
and history = history_item ref
[@@deriving show]

type heap = {
  log : history ref; (* tracks the tip *)
  constraints : tm list ref;
}
[@@deriving show]

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
let backtrack heap last_choice_point =
  backtrack heap.log heap.constraints last_choice_point

let checkpoint (heap : heap) : history = !(heap.log)

let init_heap constraints =
  let top = ref Top in
  { log = ref top; constraints = ref constraints }

type goal = tm
[@@deriving show]

type rule = int * tm * tm list * tm list
[@@deriving show]
type rules = rule list
[@@deriving show]

(******************************* unif ****************************)

let rec fold_left2 f l1 l2 = match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> f x y && fold_left2 f xs ys
  | _ -> false

let rec heapify s = function
  | App(c,l) -> App(c,List.map (heapify s) l)
  | Var _ as x -> x
  | Arg i when s.(i) != dummy -> s.(i)
  | Arg i -> let t = Var (ref dummy) in s.(i) <- t; t

let rec unif (trail:heap) (sb:tm array) (a:tm) (b:tm) = match a, b with
  | Arg _, _ -> assert false

  (* deref *)
  | Var r, _ when !r != dummy -> unif trail sb !r b
  | _, Var r when !r != dummy -> unif trail sb a !r
  | _, Arg i when sb.(i) != dummy -> unif trail sb a sb.(i)

  (* assign *)
  | Var r, _ -> assign trail r (heapify sb b); true
  | _, Var r -> assign trail r a; true (* missing OC *)
  | _, Arg i -> sb.(i) <- a; true

  | App(c1,args1), App(c2,args2) ->
    if c1 <> c2 then false
    else fold_left2 (unif trail sb) args1 args2

(******************************* table ****************************)

type canonical_goal = tm
[@@deriving show]

let abstract ?from g =
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
        | exception Not_found ->
            Var r
        end
    | App(s,args) ->
        let args = List.map aux args in
        App(s,args)
  in
  let abstract = aux g in
  (!i, !m), abstract
    
let abstract_constraints from constraints =
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

(* we could canonify g and then Stdlib.compare (OC can be expensive)*)

  module DT : sig
    
    type 'a t
    val empty : 'a t
    val add : canonical_goal -> 'a -> 'a t -> 'a t
    val mem : canonical_goal -> 'a t -> bool
    val find : canonical_goal -> 'a t -> 'a
    val remove : canonical_goal -> 'a t -> 'a t
    val iter : ((string * int) list -> 'a -> unit) -> 'a t -> unit
    val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

  end = struct
    
    type path_string_elem = string * int
    [@@deriving show]
    type path_string_elem_list = path_string_elem list
    [@@deriving show]
    let rec path_string_of = function
      | Arg i -> [string_of_int i, 0]
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

  let pp f fmt t =
    let p k v = Format.fprintf fmt "@[<hov 2>%a |->@ %a@]@ " pp_path_string_elem_list k f v in
    Format.fprintf fmt "@[<hov>";
    iter p t;
    Format.fprintf fmt "@]"

end

(******************************* run ****************************)

type continuation =
  | Done
  | ExitSLGRoot of { heap : heap; next : continuation; alts : alt list }
  | TableSolution of canonical_goal * tm
  | SolveGoals of {
      brothers : goal list;
      cutinfo : alt list; [@printer (fun _ _ -> ())] (* in elpi this is kept by passing it to run for the immediate brothers *)
      next : continuation;
    }
and alt = 
  | UnblockSLGGenerator of int (* a ! did not fire *)
  | ExploreAnotherSLDPath of {
      choice_point : history; [@printer (fun _ _ -> ())]
      goal: goal;
      rules : rule list; [@printer (fun _ _ -> ())]
      next : continuation; [@printer (fun _ _ -> ())]
}

let pp_alt fmt = function
 | ExploreAnotherSLDPath { rules; goal; _ } -> Format.fprintf fmt "(%a | %a)" pp_tm goal pp_rules rules
 | UnblockSLGGenerator i -> Format.fprintf fmt "unblock %d" i

let rec flatten_frame = function
  | SolveGoals { brothers; next; _ } ->
      let goals, action = flatten_frame next in
      brothers @ goals, action
  | x -> [], x

let pp_end_frame fmt = function
  | Done -> Format.fprintf fmt "Done"
  | ExitSLGRoot _ -> Format.fprintf fmt "ExitSLGRoot"
  | TableSolution(cg, sol) -> Format.fprintf fmt "TableSolution %a to %a" pp_tm sol pp_tm cg
  | _ -> assert false

let pp_continuation fmt continuation =
  let brothers, siblings = flatten_frame continuation in
    Format.fprintf fmt "%a; %a"
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f "; ") pp_tm) brothers
      pp_end_frame siblings

type alts = alt list

let pp_alts fmt l =
  Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f "; ")
    pp_alt fmt l
    
let all_rules = ref []
let gas = ref 0

let tabled = function
  | App(s,_) -> s.[0] = '_'
  | _ -> false

type table_entry_status = Incomplete | Complete
[@@deriving show]

let table = ref DT.empty

let pp_table fmt dt =
 DT.iter (fun _ (l,s) -> Format.fprintf fmt "(%a, [%a])@ " pp_table_entry_status s (Format.pp_print_list pp_rule) l) dt

let table_reset () = table := DT.empty

let consistent _ _ = true

let rec select (heap : heap) goal = function
  | [] -> None
  | (stack,hd,csts,conds)::rules ->
    let stack = Array.init stack (fun _ -> dummy) in
    [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a /// %a :- %a %a." pp_tm goal pp_tm hd pp_tm (App("|",csts)) pp_tm (App("&",conds))) ()];
    let prev = checkpoint heap in
    if not (unif heap stack goal hd) then begin
      backtrack heap prev;
      select heap goal rules
    end else begin
      let csts = List.map (heapify stack) csts in
      if consistent csts !(heap.constraints) then begin
        List.iter (add_cs heap) csts;
        Some (prev, List.map (heapify stack) conds, rules)
      end else begin
        backtrack heap prev;
        select heap goal rules
      end
    end

let new_table_entry cgoal =
  table := DT.add cgoal ([],Incomplete) !table

type slg_consumer = {
  goal : goal;
  next : continuation;
  heap : heap;
  checkpoint : history;
}
[@@deriving show]

type generator =
| Root of {
    initial_goal : (int * tm * tm list);
    rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
  }
| UnexploredBranches of heap * alt list
[@@deriving show]

let init_tree (stack,cg,cs) =
  let stack = Array.init stack (fun _ -> dummy) in
  let g = heapify stack cg in
  let cs = List.map (heapify stack) cs in
  g, init_heap cs


module IM = Map.Make(struct type t = int let compare = Stdlib.compare end)

type slg_status = {
  consumers : slg_consumer list DT.t;
  generators : generator list;
  stuck_generators : generator IM.t; [@printer (fun fmt m -> IM.iter (fun _ -> pp_generator fmt) m)]
  resume_queue : (slg_consumer * rule) list;
  root_alts : (heap * alts) option;
}
[@@deriving show]

let empty_slg_status = {
  consumers = DT.empty;
  generators = []; stuck_generators = IM.empty;
  resume_queue = [];
  root_alts = None;
}

type sld_status = {
  goal : goal;
  next : continuation;
  heap : heap;
  cutinfo : alts;
  rules : rule list;
  alts : alts;
}

let dt_append k v t =
  try
    let old = DT.find k t in
    DT.add k (old @ [v]) t
  with Not_found ->
    DT.add k [v] t

    
    
let push_consumer cgoal (c : slg_consumer) (s : slg_status) =
  { s with consumers = dt_append cgoal c s.consumers }

let push_generator (g : generator) (s : slg_status) =
  { s with generators = g :: s.generators }

let push_stuck_generator = let nonce = ref 0 in
 fun (g : generator) (s : slg_status) ->
 incr nonce;
 !nonce, { s with stuck_generators = IM.add !nonce g s.stuck_generators }

let pop_stuck_generator i ({ stuck_generators; _ } as s) =
  assert(IM.mem i stuck_generators);
  let g = IM.find i stuck_generators in
  push_generator g { s with stuck_generators = IM.remove i stuck_generators }

let set_root_if_not_set heap alts s =
  if s.root_alts = None then { s with root_alts = Some(heap, alts) } else s

let resume_all_consumers cgoal (c : rule) (s : slg_status) =
  try
    let consumers = DT.find cgoal s.consumers in
    {s with resume_queue = List.map (fun x -> x,c) consumers @ s.resume_queue }
  with Not_found ->
    assert false
  
let table_solution cgoal solution constraints s =
  match DT.find cgoal !table with
  | solutions, status ->
      let abstract_map, solution = abstract solution in
      let nvars, constraints = abstract_constraints abstract_map constraints in
      let solution = nvars, solution, constraints, [] in
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
      { sgs with consumers = DT.remove cgoal sgs.consumers }
  | _, Complete -> assert false
  | exception Not_found -> assert false

let has_cut = List.mem cut

type result = TIMEOUT | FAIL | OK of tm list * heap * alts * slg_status

(* called on a goal as we see it for the first time *)
let rec run { goal; rules; next; alts; cutinfo; heap } (sgs : slg_status) : result =
  [%trace "run" ~rid 
    ("@[<hov 2>g: %a@ next: %a@ alts: %a@]@\n" pp_tm goal pp_continuation next pp_alts alts)
  begin 
    if tabled goal
    then enter_slg goal rules next alts cutinfo heap sgs
    else       sld goal rules next alts cutinfo heap sgs
end]

and enter_slg goal rules next alts cutinfo heap sgs =
match !gas with
  | 0 -> TIMEOUT
  | _ ->
    decr gas;
  let abstract_map, cgoal = abstract goal in
  match DT.find cgoal !table with
  | [], Incomplete ->
      [%spy "slg:suspend" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; heap; checkpoint = checkpoint heap } sgs in
      advance_slg sgs
  | answers, Complete -> (* TODO: Trie -> DT(find_unifiable) *)
      [%spy "slg:complete->sld" ~rid pp_tm cgoal];
      sld goal answers next alts cutinfo heap sgs
  | answers, Incomplete ->
      [%spy "slg:incomplete->sld+slg" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; heap; checkpoint = checkpoint heap } sgs in
      sld goal answers next alts cutinfo heap sgs
  | exception Not_found ->
      [%spy "slg:new" ~rid pp_tm cgoal];
      let sgs = set_root_if_not_set heap alts sgs in
      let sgs = push_consumer cgoal { goal; next = ExitSLGRoot { heap; next; alts }; heap; checkpoint = checkpoint heap } sgs in
      new_table_entry cgoal;
      let nvars, cconstraints = abstract_constraints abstract_map !(heap.constraints) in
      let sgs = push_generator (Root { initial_goal = (nvars,cgoal,cconstraints); rules }) sgs in
      advance_slg sgs

and advance_slg ({ generators; resume_queue; root_alts; _ } as s) =
  [%trace "slg:step" ~rid ("@[<hov 2>%a@ table:@[<hov 2>%a@]@]\n" pp_slg_status s pp_table !table)
  begin match resume_queue with
  | ({goal ; next; heap; checkpoint }, solution) :: resume_queue ->
      let s = { s with resume_queue } in
      backtrack heap checkpoint;
      begin match select heap goal [solution] with
      | None -> advance_slg s
      | Some(_,[],[]) -> pop_andl next [] heap s (* #1 *)
      | _ -> assert false (* solutions have no subgoals *)
      end
  | [] ->
     match generators with
     | [] ->
        begin match root_alts with
        | None -> FAIL
        | Some (heap,alts) ->
            next_alt heap alts { s with root_alts = None }
        end
     | UnexploredBranches (_,[]) :: generators -> advance_slg { s with generators }
     | UnexploredBranches (heap,alts) :: generators ->
        next_alt heap alts { s with generators }
     | Root { initial_goal = (_, cgoal,_); rules = []; _ } :: generators ->
        let s = table_entry_complete cgoal s in (* TODO: do this more ofted/early *)
        advance_slg { s with generators }
     | Root { initial_goal; rules } :: generators ->
        let _, cgoal, _ = initial_goal in
        let goal, heap = init_tree initial_goal in
        match select heap goal rules with
        | None -> advance_slg { s with generators }
        | Some (_,[], rules) ->
            let s = { s with generators = Root { initial_goal; rules } :: generators } in
            pop_andl (TableSolution(cgoal,goal)) [] heap s
        | Some (_,ngoal::brothers, rules) ->
            let s = { s with generators } in
            if rules <> [] && has_cut (ngoal :: brothers) then
              let nonce, s = push_stuck_generator (Root { initial_goal; rules }) s in
              let next = SolveGoals { brothers; cutinfo = []; next = TableSolution(cgoal,goal) } in
              run { goal = ngoal; next; alts = [UnblockSLGGenerator nonce]; rules = !all_rules; cutinfo = []; heap; } s        
            else
              let s = push_generator (Root { initial_goal; rules }) s in
              let next = SolveGoals { brothers; cutinfo = []; next = TableSolution(cgoal,goal) } in
              run { goal = ngoal; next; alts = []; rules = !all_rules; cutinfo = []; heap } s        
end]

and sld goal rules next (alts : alts) (cutinfo : alts) (heap:heap) (sgs : slg_status) =
match !gas with
| 0 -> TIMEOUT
| _ ->
  decr gas;
  if goal = cut then pop_andl next cutinfo heap sgs
  else 
    match select heap goal rules with
    | None -> next_alt heap alts sgs
    | Some (_, [], []) -> pop_andl next alts heap sgs
    | Some (choice_point, [], rules) ->
        let alts = ExploreAnotherSLDPath { goal; rules; next; choice_point } :: alts in
        pop_andl next alts heap sgs
    | Some (choice_point, ngoal :: brothers, rules) ->
        let old_alts = alts in
        let alts = ExploreAnotherSLDPath { goal; rules; next; choice_point } :: alts in
        let next = SolveGoals { brothers; cutinfo = old_alts; next } in
        run { goal = ngoal; rules = !all_rules; next; alts; cutinfo = old_alts; heap } sgs

and pop_andl (next : continuation) (alts : alts) (heap : heap) (sgs : slg_status) =
  [%trace "pop_andl" ~rid ("@[<hov 2>next: %a / alts: %a]@\n" pp_continuation next pp_alts alts) begin
  match next with
  | Done -> OK (!(heap.constraints),heap,alts,sgs)
  | ExitSLGRoot { heap; next; alts = o } -> assert(alts = [] (* #1 *)); pop_andl next o heap sgs
  | TableSolution(cgoal,solution) ->
      let sgs, progress = table_solution cgoal solution !(heap.constraints) sgs in
      if progress then
        let sgs = if alts != [] then push_generator (UnexploredBranches (heap,alts)) sgs else sgs in
        advance_slg sgs
      else
        next_alt heap alts sgs
  | SolveGoals { brothers = []; next; _ } -> pop_andl next alts heap sgs
  | SolveGoals { brothers = goal :: brothers; cutinfo; next } ->
      run { goal; rules = !all_rules;
            next = SolveGoals { brothers = brothers; cutinfo; next };
            alts; cutinfo; heap; } sgs
  end]

and next_alt (heap : heap) alts (sgs : slg_status) : result =
  [%trace "next_alt" ~rid ("@[<hov 2>%a]@\n" pp_alts alts) begin
  match alts with
  | [] -> advance_slg sgs
  | UnblockSLGGenerator nonce :: alts ->
      let sgs = pop_stuck_generator nonce sgs in
      next_alt heap alts sgs
  | ExploreAnotherSLDPath { goal; rules; next; choice_point } :: alts ->
      backtrack heap choice_point;
      sld goal rules next (alts : alts) ([] : alts) (heap:heap) (sgs : slg_status)
  end]

let run goal rules =
  let heap = init_heap [] in
  match goal with
  | [] -> assert false
  | [goal] -> run { goal; rules; next = Done; alts = []; cutinfo = []; heap } empty_slg_status
  | goal::gs -> run { goal; rules; next = SolveGoals { brothers = gs; next = Done; cutinfo = []}; alts = []; cutinfo = []; heap } empty_slg_status

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
        List.length !l, hd, csts, hyps)
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
  let program = P.parse_program program in
  let query = P.parse_query query in
  all_rules := program;
  gas := steps;
  pp_reset ();
  table_reset ();
  let rec all n = function
  | FAIL -> [Format.asprintf "no"]
  | TIMEOUT -> [Format.asprintf "steps"]
  | OK (csts,heap,alts,sgs) ->
      let g = Format.asprintf "%a" (ppl ", ") query in
      let c = if csts = [] then "" else Format.asprintf "%a| " (ppli ", ") csts in
      let s = c^g in
      if n = 1 then [s]
      else s :: all (n-1) (next_alt heap alts sgs)
  in
  all n (run query !all_rules)

let errors = ref 0
let check ?(steps=1000) (`Check(s,p,q,n,l1)) =
  let l2 = main q steps n p in
  if l1 <> l2 then begin
    incr errors;
    Format.eprintf "ERROR: %s:\nExpected: %a\nActual:   %a\n%!" s
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l1
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l2
  end else
    Format.eprintf "@[<hov 2>   %s: ok (%d steps)@]\n%!" s (steps - !gas)
    (*Format.eprintf "@[<hov 2> %s: ok (%d steps, table: @[<hov>%a@])@]\n%!" s (steps - !gas) pp_table !table*)

