
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

type env_item =
  | ReAssign of tm ref * tm
[@@deriving show]

type trail_item =
  | Assign of tm ref
  | Observer of env_item list ref list
[@@deriving show]

type trail_log = trail_item list ref
[@@deriving show]

type trail = { log : trail_log; env : env_item list ref; constraints : tm list }
[@@deriving show]

let assign { log = trail; _ }  v t =
  trail := Assign v :: !trail;
  [%spy "assign" ~rid pp_tm (Var v)];
  [%spy "assign:with" ~rid pp_tm t];
  v := t

let add_cs c t = { t with constraints = c :: t.constraints }
let del_cs c t = { t with constraints = List.filter (fun x -> x != c) t.constraints }
  

let rec redo trail = function
  | [] -> trail
  | ReAssign(r,v) :: rest -> assign trail r v; redo trail rest

let rec backtrack trail env constraints observers =
    match !trail with
    | [] -> assert false
    | Observer os :: vs ->
        if List.memq env os then begin
          let observers = List.filter (fun x -> x != env) observers in
          if observers != [] then
            trail := Observer observers :: !trail;
          !env, constraints
        end else begin
          trail := vs;
          backtrack trail env constraints (os @ observers)
        end
    | Assign v :: vs ->
        List.iter (fun o -> o := ReAssign (v,!v) :: !o) observers;
        v := dummy;
        trail := vs;
        backtrack trail env constraints observers

let backtrack { log; env; constraints } =
  let fwd, constraints = backtrack log env constraints [] in
  redo { log; env = ref []; constraints } fwd

let checkpoint { log; constraints; _ } =
  let env = ref [] in
  log := Observer [env] :: !log;
  { log; env; constraints }

let empty_trail constraints = { log = ref []; env = ref []; constraints }

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

let rec unif (trail:trail) (sb:tm array) (a:tm) (b:tm) = match a, b with
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

let rec map_acc f acc = function
  | [] -> acc, [], []
  | x :: xs ->
      let acc, y, z = f acc x in
      let acc, ys, zs = map_acc f acc xs in
      acc, y :: ys, z :: zs

let abstract ?(from = 0, PtrMap.empty ()) g =
  let i, m = from in
  let i = ref i in
  let m = ref m in
  let rec aux = function
    | Arg _ -> assert false
    | Var r when !r <> dummy -> aux !r
    | Var r ->
        begin match PtrMap.find r !m with
        | n -> Arg(n)
        | exception Not_found ->
            m := PtrMap.add r !i !m;
            let x = Arg !i in
            incr i;
            x
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
  let rec fixpoint from relevant irrelevant =
    let changed, from, relevant, irrelevant = aux from relevant irrelevant false irrelevant in
    if changed then fixpoint from relevant irrelevant
    else fst from, relevant
  in
  let constraints = List.map (fun c -> abstract c, c) constraints in
  fixpoint from [] constraints

let clausify_solution t csts =
  let m = ref [] in
  let rec aux = function
  | Arg _ -> assert false
  | Var r when !r <> dummy -> aux !r
  | Var r -> 
      begin try
        List.assq r !m
      with Not_found ->
        m := (r, Arg(List.length !m)) :: !m;
        List.assq r !m
      end
  | App(s,args) ->
      App(s,List.map aux args)
  in
  let t = aux t in
  let csts = List.map aux csts in
  List.length !m, t, csts, []

(* we could canonify g and then Stdlib.compare (OC can be expensive)*)

  module DT : sig
    
    type 'a t
    val empty : 'a t
    val add : canonical_goal -> 'a -> 'a t -> 'a t
    val mem : canonical_goal -> 'a t -> bool
    val find : canonical_goal -> 'a t -> 'a
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
  let iter f t = iter f t

  let pp f fmt t =
    let p k v = Format.fprintf fmt "@[<hov 2>%a |->@ %a@]@ " pp_path_string_elem_list k f v in
    Format.fprintf fmt "@[<hov>";
    iter p t;
    Format.fprintf fmt "@]"

end

(******************************* run ****************************)

type frame =
  | Done
  | SLGRoot of { next : frame; alts : alt list }
  | TableSolution of canonical_goal * tm
  | Todo of {
      brothers : goal list;
      cutinfo : alt list; [@printer (fun _ _ -> ())]
      siblings : frame;
    }
and alt = 
  | Unblock of int
  | Alt of {
  goal: goal;
  rules : rule list; [@printer (fun _ _ -> ())]
  stack : frame; [@printer (fun _ _ -> ())]
  trail : trail; [@printer (fun _ _ -> ())]
  cutinfo : alt list; [@printer (fun _ _ -> ())]
}

let pp_alt fmt = function
 | Alt { rules; goal; _ } -> Format.fprintf fmt "%a | %a" pp_tm goal pp_rules rules
 | Unblock i -> Format.fprintf fmt "%d" i

let rec flatten_frame = function
  | Todo { brothers; siblings; _ } ->
      let goals, action = flatten_frame siblings in
      brothers @ goals, action
  | x -> [], x

let pp_end_frame fmt = function
  | Done -> Format.fprintf fmt "Done"
  | SLGRoot _ -> Format.fprintf fmt "SLGRoot"
  | TableSolution(cg, sol) -> Format.fprintf fmt "TableSolution %a to %a" pp_tm sol pp_tm cg
  | _ -> assert false

let pp_frame fmt frame =
  let brothers, siblings = flatten_frame frame in
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

let rec select trail goal = function
  | [] -> None
  | (stack,hd,csts,conds)::rules ->
    let stack = Array.init stack (fun _ -> dummy) in
    [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a /// %a :- %a." pp_tm goal pp_tm hd pp_tm (App("&",conds))) ()];
    let trail = checkpoint trail in
    if not (unif trail stack goal hd) then begin
      let trail = backtrack trail in
      select trail goal rules
    end else begin
      let csts = List.map (heapify stack) csts in
      if consistent csts trail.constraints then
        Some ({trail with constraints = trail.constraints @ csts }, List.map (heapify stack) conds, rules)
      else
        let trail = backtrack trail in
        select trail goal rules
    end

let new_table_entry cgoal =
  table := DT.add cgoal ([],Incomplete) !table

type consumer = {
  next : frame;
  goal : tm;
  trail : trail;
}
[@@deriving show]

type generator = {
  initial_goal : (int * tm * tm list);
  rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
}
[@@deriving show]

let init_tree (stack,cg,cs) =
  let stack = Array.init stack (fun _ -> dummy) in
  let g = heapify stack cg in
  let cs = List.map (heapify stack) cs in
  g, empty_trail cs


module IM = Map.Make(struct type t = int let compare = Stdlib.compare end)

type slg_status = {
  consumers : consumer list DT.t;
  generators : generator list;
  stuck_generators : generator IM.t; [@printer (fun fmt m -> IM.iter (fun _ -> pp_generator fmt) m)]
  resume_queue : (consumer * rule) list;
  root : alts option;
}
[@@deriving show]

let empty_slg_status = {
  consumers = DT.empty;
  generators = []; stuck_generators = IM.empty;
  resume_queue = [];
  root = None;
}

type sld_status = {
  goal : goal;
  rules : rule list;
  next : frame;
  trail : trail;
  alts : alts;
  cutinfo : alts;
}

let dt_append k v t =
  try
    let old = DT.find k t in
    DT.add k (old @ [v]) t
  with Not_found ->
    DT.add k [v] t

    
    
let push_consumer cgoal (c : consumer) (s : slg_status) =
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

let set_root_if_not_set alts s =
  if s.root = None then { s with root = Some alts } else s
let unset_root s = { s with root = None }

let resume_all_consumers cgoal (c : rule) (s : slg_status) =
  try
    let consumers = DT.find cgoal s.consumers in
    {s with resume_queue = List.map (fun x -> x,c) consumers @ s.resume_queue }
  with Not_found ->
    s
  
let table_solution cgoal solution constraints s =
  match DT.find cgoal !table with
  | solutions, status ->
      let solution = clausify_solution solution constraints in
      if List.mem solution solutions then
        s
      else begin
        table := DT.add cgoal (solutions @ [solution], status) !table;
        resume_all_consumers cgoal solution s
      end
  | exception Not_found -> assert false
    
let table_entry_complete cgoal =
  match DT.find cgoal !table with
  | solutions, Incomplete ->
      table := DT.add cgoal (solutions, Complete) !table
  | _, Complete -> assert false
  | exception Not_found -> assert false

let has_cut = List.mem cut

type result = TIMEOUT | FAIL | OK of tm list * alts * slg_status


let rec run { goal; rules; next; alts; cutinfo; trail } (sgs : slg_status) : result =
  [%trace "run" ~rid 
    ("@[<hov 2>g: %a@ next: %a@ alts: %a@]@\n" pp_tm goal pp_frame next pp_alts alts)
  begin match !gas with
  | 0 -> TIMEOUT
  | _ ->
    decr gas;
    if tabled goal then enter_slg goal rules next alts cutinfo trail sgs
    else sld goal rules next alts cutinfo trail sgs
end]

and enter_slg goal rules next alts cutinfo trail sgs =
  let abstract_map, cgoal = abstract goal in
  match DT.find cgoal !table with
  | [], Incomplete ->
      [%spy "slg:suspend" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; trail = checkpoint trail } sgs in
      advance_slg sgs
  | answers, Complete -> (* TODO: Trie -> DT(find_unifiable) *)
      [%spy "slg:complete->sld" ~rid pp_tm cgoal];
      sld goal answers next alts cutinfo trail sgs
  | answers, Incomplete ->
      [%spy "slg:incomplete->sld+slg" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; trail = checkpoint trail } sgs in
      sld goal answers next alts cutinfo trail sgs
  | exception Not_found ->
      [%spy "slg:new" ~rid pp_tm cgoal];
      let sgs = set_root_if_not_set alts sgs in
      let sgs = push_consumer cgoal { goal; next = SLGRoot { next; alts }; trail = checkpoint trail } sgs in
      new_table_entry cgoal;
      let nvars, cconstraints = abstract_constraints abstract_map trail.constraints in
      let sgs = push_generator { initial_goal = (nvars,cgoal,cconstraints); rules } sgs in
      advance_slg sgs

and advance_slg ({ generators; resume_queue; root; _ } as s) =
  [%trace "slg:step" ~rid ("@[<hov 2>%a@ table:@[<hov 2>%a@]@]\n" pp_slg_status s pp_table !table)
  begin match resume_queue with
  | ({goal ; next; trail }, solution) :: resume_queue ->
      let s = { s with resume_queue } in
      let trail = backtrack trail in
      begin match select trail goal [solution] with
      | None -> advance_slg s
      | Some(trail,[],[]) -> pop_andl next [] trail s
      | _ -> assert false (* solutions have no subgoals *)
      end
  | [] ->
     match generators with
     | [] ->
        begin match root with
        | None -> FAIL
        | Some alts ->
            let s = unset_root s in
            next_alt alts s
        end
     | { initial_goal = (_, cgoal,_); rules = []; _ } :: generators ->
          table_entry_complete cgoal; (* TODO: do this more ofted/early *)
          advance_slg { s with generators }
     | { initial_goal; rules } :: generators ->
        let _, cgoal, _ = initial_goal in
        let goal, trail = init_tree initial_goal in
        match select trail goal rules with
        | None -> advance_slg { s with generators }
        | Some (trail,[], rules) ->
            let s = { s with generators = { initial_goal; rules } :: generators } in
            pop_andl (TableSolution(cgoal,goal)) [] trail s
        | Some (trail,ngoal::brothers, rules) ->
            let s = { s with generators } in
            if rules <> [] && has_cut (ngoal :: brothers) then
              let nonce, s = push_stuck_generator { initial_goal; rules } s in
              let next = Todo { brothers; cutinfo = []; siblings = (TableSolution(cgoal,goal)) } in
              run { goal = ngoal; next; alts = [Unblock nonce]; rules = !all_rules; cutinfo = []; trail } s        
            else
              let s = push_generator { initial_goal; rules } s in
              let next = Todo { brothers; cutinfo = []; siblings = (TableSolution(cgoal,goal)) } in
              run { goal = ngoal; next; alts = []; rules = !all_rules; cutinfo = []; trail } s        
end]

and sld goal rules next (alts : alts) (cutinfo : alts) trail (sgs : slg_status) =
  if goal = cut then pop_andl next cutinfo trail sgs
  else 
    let trail = checkpoint trail in
    match select trail goal rules with
    | None -> next_alt alts sgs
    | Some (trail, [], []) -> pop_andl next alts trail sgs
    | Some (trail, [], rules) ->
        let alts = Alt { goal; rules; stack=next; trail; cutinfo } :: alts in
        pop_andl next alts trail sgs
    | Some (trail, ngoal :: brothers, rules) ->
        let old_alts = alts in
        let alts = Alt { goal; rules; stack=next; trail; cutinfo } :: alts in
        let next = Todo { brothers; cutinfo; siblings = next } in
        run { goal = ngoal; rules = !all_rules; next; alts; cutinfo = old_alts; trail } sgs

and pop_andl (next : frame) (alts : alts) (trail : trail) (sgs : slg_status) =
  [%trace "pop_andl" ~rid ("@[<hov 2>%a]@\n" pp_frame next) begin
  match next with
  | Done -> OK (trail.constraints,alts,sgs)
  | SLGRoot { next; alts = o } -> assert(alts = []); pop_andl next o trail sgs
  | TableSolution(cgoal,solution) ->
      let sgs = table_solution cgoal solution trail.constraints sgs in
      advance_slg sgs
  | Todo { brothers = []; siblings = next; _ } -> pop_andl next alts trail sgs
  | Todo { brothers = goal :: brothers; cutinfo; siblings } ->
      run { goal; rules = !all_rules;
            next = Todo { brothers = brothers; cutinfo; siblings };
            alts; cutinfo; trail } sgs
  end]
and next_alt alts (sgs : slg_status) : result = match alts with
  | [] -> advance_slg sgs
  | Unblock nonce :: alts ->
      let sgs = pop_stuck_generator nonce sgs in
      next_alt alts sgs
  | Alt { goal; rules; stack=next; trail; cutinfo } :: alts ->
      let trail = backtrack trail in
      run { goal; rules; next; alts; cutinfo; trail } sgs

let run goal rules =
  let trail = empty_trail [] in
  match goal with
  | [] -> assert false
  | [goal] -> run { goal; rules; next = Done; alts = []; cutinfo = []; trail } empty_slg_status
  | goal::gs -> run { goal; rules; next = Todo { brothers = gs; siblings = Done; cutinfo = []}; alts = []; cutinfo = []; trail } empty_slg_status

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
  | OK (csts,alts,sgs) ->
      let g = Format.asprintf "%a" (ppl ", ") query in
      let c = if csts = [] then "" else Format.asprintf "%a| " (ppli ", ") csts in
      let s = c^g in
      if n = 1 then [s]
      else s :: all (n-1) (next_alt alts sgs)
  in
  all n (run query !all_rules)

let errors = ref 0
let check ?(steps=1000) (`Check(s,p,q,n,l1)) =
  let l2 = main q steps n p in
  if l1 <> l2 then begin
    incr errors;
    Format.eprintf "ERROR: %s:\n%a\n%a\n%!" s
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l1
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l2
  end else
    Format.eprintf "@[<hov 2> %s: ok (%d steps)@]\n%!" s (steps - !gas)
    (*Format.eprintf "@[<hov 2> %s: ok (%d steps, table: @[<hov>%a@])@]\n%!" s (steps - !gas) pp_table !table*)

