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
  | Arg i -> Format.fprintf fmt "_%d_" i

let pp_tm = pp
let ppl s = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f s) pp

(******************************* backtrack ****************************)
type trail_log = tm ref list ref
[@@deriving show]
type fwd_trail = (tm ref * tm) list
[@@deriving show]

type trail = { log : trail_log; old_trail : tm ref list }
[@@deriving show]

let assign { log = trail; _ }  v t =
  trail := v :: !trail;
  [%spy "assign" ~rid pp_tm (Var v)];
  [%spy "assign:with" ~rid pp_tm t];
  v := t

let empty_trail () = let bottom = [] in { log = ref bottom; old_trail = bottom }

let rec backtrack ?(already_undone=false) ({ log = trail; old_trail = o } as t) =
  if o != !trail then begin
    match !trail with
    | [] ->
        if already_undone then () else assert false
    | v :: vs ->
        v := dummy;
        trail := vs;
        backtrack ~already_undone t
  end

let rec chop_trail o trail =
  if o != trail then
    match trail with
    | [] -> assert false
    | v :: vs -> v :: chop_trail o vs
  else
     []
let chop_trail trail o = chop_trail o !trail

let rec redo trail = function
  | [] -> ()
  | (r,v) :: rest -> assign trail r v; redo trail rest

let rec copy_trail = function
  | [] -> []
  | r :: trail -> (r, !r) :: copy_trail trail
let copy_trail { log; _ } = copy_trail !log

let checkpoint { log; _ } = { log; old_trail = !log }

type goal = tm
[@@deriving show]

type rule = int * tm * tm list
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

let rec unif (trail:trail) (s:tm array) (a:tm) (b:tm) = match a, b with
  (* deref *)
  | Var r, _ when !r != dummy -> unif trail s !r b
  | _, Var r when !r != dummy -> unif trail s a !r
  | _, Arg i when s.(i) != dummy -> unif trail s a s.(i)
  | Arg _, _ -> assert false

  (* assign *)
  | Var r, _ -> assign trail r (heapify s b); true
  | _, Var r -> assign trail r a; true (* missing OC *)
  | _, Arg i -> s.(i) <- a; true

  | App(c1,args1), App(c2,args2) ->
    if c1 <> c2 then false
    else fold_left2 (unif trail s) args1 args2

(******************************* table ****************************)

type canonical_goal = tm
[@@deriving show]

let canonical_names = [|
  App("$0",[]) ;
  App("$1",[]) ;
  App("$2",[]) ;
  App("$3",[]) ;
  App("$4",[]) ;
  App("$5",[]) ;
  App("$6",[]) ;
  App("$7",[]) ;
  App("$8",[]) ;
  App("$9",[]) ;
|]

let rec map_acc f acc = function
  | [] -> acc, []
  | x :: xs ->
      let acc, y = f acc x in
      let acc, ys = map_acc f acc xs in
      acc, y :: ys

let rec canonify trail i (g : tm) : int * canonical_goal =
  match g with
  | Arg _ -> assert false
  | Var r when !r <> dummy -> (canonify trail) i !r
  | Var r -> assign trail r canonical_names.(i); i+1, !r
  | App(s,args) ->
      let i, args = map_acc (canonify trail) i args in
      i, App(s,args)

let copy g =
  let trail = empty_trail () in
  let n, _ = canonify trail 0 g in
  backtrack trail;
  let v = Array.init n (fun _ -> ref @@ Var (ref dummy)) in
  let rec aux i = function
    | Arg _ -> assert false
    | Var r when !r <> dummy -> aux i !r
    | Var _ -> i+1, Var(v.(i))
    | App(s,args) ->
      let i, args = map_acc aux i args in
      i, App(s,args)
  in
    snd @@ aux 0 g

let rec ground = function
  | Arg _ -> assert false
  | Var r when !r <> dummy -> ground !r
  | Var _ -> assert false
  | App(s,args) ->
      App(s,List.map ground args)

let canonify (g : tm) : canonical_goal =
  let trail = empty_trail () in
  let _, g = canonify trail 0 g in
  backtrack trail;
  g

(* we could canonify g and then Stdlib.compare (OC can be expensive)*)
let variant (c : canonical_goal) (g : goal) =
  let trail = empty_trail () in
  let u = unif trail [||] g c in (* pass g on the left to avoid heapify on assign *)
  backtrack trail;
  u

  module DT : sig
    
    type 'a t
    val empty : 'a t
    val add : canonical_goal -> 'a -> 'a t -> 'a t
    val mem : canonical_goal -> 'a t -> bool
    val find : canonical_goal -> 'a t -> 'a

  end = struct
    
    type path_string_elem = string * int
    let rec path_string_of = function
      | Arg _ -> assert false
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

end

(******************************* run ****************************)

type frame =
  | Done
  | Root of frame * alt list
  | Contribute of tm * canonical_goal
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
  | Root _ -> Format.fprintf fmt "Root"
  | Contribute(sol,cg) -> Format.fprintf fmt "Contribute %a to %a" pp_tm sol pp_tm cg
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

let table = ref DT.empty

let table_reset () = table := DT.empty

let rec select trail goal = function
  | [] -> None
  | (stack,hd,conds)::rules ->
    [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a /// %a :- %a." pp_tm goal pp_tm hd pp_tm (App("&",conds))) ()];
    let stack = Array.init stack (fun _ -> dummy) in
    if not (unif trail stack goal hd) then begin
      backtrack trail;
      select trail goal rules
    end else begin
      Some (List.map (heapify stack) conds, rules)
    end

let new_table_entry cgoal =
  table := DT.add cgoal ([],Incomplete) !table

type consumer = {
  next : frame;
  goal : tm;
  trail : trail;
  env : fwd_trail;
}
[@@deriving show]

type generator = {
  goal : tm;
  rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
  next : frame;
  trail : trail;
}
[@@deriving show]

module IM = Map.Make(struct type t = int let compare = Stdlib.compare end)

type slg_status = {
  consumers : consumer list DT.t; [@printer (fun _ _ -> ())]
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
  
let table_solution cgoal solution s =
  match DT.find cgoal !table with
  | solutions, status ->
      let solution = 0, ground solution, [] in
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

type result = TIMEOUT | FAIL | OK of alts * slg_status


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
  let cgoal = canonify goal in
  match DT.find cgoal !table with
  | [], Incomplete ->
      [%spy "slg:suspend" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; trail = checkpoint trail; env = copy_trail trail } sgs in
      advance_slg sgs
  | answers, Complete ->
      [%spy "slg:complete->sld" ~rid pp_tm cgoal];
      sld goal answers next alts cutinfo trail sgs
  | answers, Incomplete ->
      [%spy "slg:incomplete->sld+slg" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next; trail = checkpoint trail; env = copy_trail trail } sgs in
      sld goal answers next alts cutinfo trail sgs
  | exception Not_found ->
      [%spy "slg:new" ~rid pp_tm cgoal];
      let sgs = set_root_if_not_set alts sgs in
      let sgs = push_consumer cgoal { goal; next = Root(next,alts); trail = checkpoint trail; env = copy_trail trail } sgs in
      new_table_entry cgoal;
      let trail = empty_trail () in
      let goal = copy goal in (* also copy the program *)
      let sgs = push_generator { trail; goal; rules; next = Contribute(goal,cgoal) } sgs in
      advance_slg sgs

and advance_slg ({ generators; resume_queue; root; _ } as s) =
  [%trace "slg:step" ~rid ("@[<hov 2>%a]@\n" pp_slg_status s)
  begin match resume_queue with
  | ({goal ; next; trail; env }, solution) :: resume_queue ->
      let s = { s with resume_queue } in
      backtrack ~already_undone:true trail;
      redo trail env;
      begin match select trail goal [solution] with
      | None -> advance_slg s
      | Some([],[]) -> pop_andl next [] trail s
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
     | { rules = []; next = Contribute(_,cgoal); _ } :: generators ->
          table_entry_complete cgoal;
          advance_slg { s with generators }
     | { rules = []; _ } :: generators -> advance_slg { s with generators }
     | { trail; goal; next; rules } :: generators ->
        backtrack trail;
        match select trail goal rules with
        | None -> advance_slg { s with generators }
        | Some ([], rules) ->
            let s = { s with generators = { trail; goal; next; rules } :: generators } in
            pop_andl next [] trail s
        | Some (ngoal::brothers, rules) ->
            let s = { s with generators } in
            if rules <> [] && has_cut (ngoal :: brothers) then
              let nonce, s = push_stuck_generator { trail; goal; next; rules } s in
              let next = Todo { brothers; cutinfo = []; siblings = next } in
              run { goal = ngoal; next; alts = [Unblock nonce]; rules = !all_rules; cutinfo = []; trail } s        
            else
              let s = push_generator { trail; goal; next; rules } s in
              let next = Todo { brothers; cutinfo = []; siblings = next } in
              run { goal = ngoal; next; alts = []; rules = !all_rules; cutinfo = []; trail } s        
end]

and sld goal rules next (alts : alts) (cutinfo : alts) trail (sgs : slg_status) =
  if goal = cut then pop_andl next cutinfo trail sgs
  else 
    let trail = checkpoint trail in
    match select trail goal rules with
    | None -> next_alt alts sgs
    | Some ([], []) -> pop_andl next alts trail sgs
    | Some ([], rules) ->
        let alts = Alt { goal; rules; stack=next; trail; cutinfo } :: alts in
        pop_andl next alts trail sgs
    | Some (ngoal :: brothers, rules) ->
        let old_alts = alts in
        let alts = Alt { goal; rules; stack=next; trail; cutinfo } :: alts in
        let next = Todo { brothers; cutinfo; siblings = next } in
        run { goal = ngoal; rules = !all_rules; next; alts; cutinfo = old_alts; trail } sgs

and pop_andl (next : frame) (alts : alts) (trail : trail) (sgs : slg_status) =
  [%trace "pop_andl" ~rid ("@[<hov 2>%a]@\n" pp_frame next) begin
  match next with
  | Done -> OK (alts,sgs)
  | Root(next, alts) -> pop_andl next alts trail sgs
  | Contribute(solution,cgoal) ->
      let sgs = table_solution cgoal solution sgs in
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
      backtrack trail;
      run { goal; rules; next; alts; cutinfo; trail } sgs

let run goal rules =
  let trail = empty_trail () in
  match goal with
  | [] -> assert false
  | [goal] -> run { goal; rules; next = Done; alts = []; cutinfo = []; trail } empty_slg_status
  | goal::gs -> run { goal; rules; next = Todo { brothers = gs; siblings = Done; cutinfo = []}; alts = []; cutinfo = []; trail } empty_slg_status

(***************************** TEST *************************)
module P = struct

  let l = ref []
  let rec vars = function
    | App(s,[]) ->
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
    | App(x,xs) -> App(x,List.map vars xs)
    | x -> x
  

  let parse_program s = try
    let lexbuf = Lexing.from_string s in
    let cl = Parser.program Lexer.token lexbuf in
    cl |> List.map (fun (hd,hyps) ->
        l := [];
        let hd = vars hd in
        let hyps = List.map vars hyps in
        List.length !l, hd, hyps)
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
  | OK (alts,sgs) ->
      let s = Format.asprintf "%a" (ppl ", ") query in
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
    Format.eprintf "%s: ok (%d steps)\n%!" s (steps - !gas)

let () =
  let filters = Trace_ppx_runtime.Runtime.parse_argv (List.tl @@ Array.to_list Sys.argv) in

  let checks = [

  `Check("transitive closure loops instead of fail",
      "
      t(a,b).
      t(a,c).
      t(b,d).
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      ",
    "t(a,X)", 4, ["t(a, b)"; "t(a, c)"; "t(a, d)"; "steps"]);

  `Check("transitive closure loops before producing any solution",
      "
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      t(a,b).
      t(a,c).
      t(b,d).
      ",
    "t(a,X)", 1, ["steps"]);

  `Check("cutting the solution is failure",
      "
      t :- !, fail.
      t.
      ",
    "t", 1, ["no"]);

  `Check("cutting nothing is noop",
      "
      t.
      t :- !, fail.
      ",
    "t", 2, ["t"; "no"]);

  `Check("tail cut kills alternatives",
      "
      t.
      t.
      p :- t, !.
      ",
    "p", 2, ["p"; "no"]);

  `Check("tail cut removed, more solutions",
      "
      t.
      t.
      p :- t.
      ",
    "p", 3, ["p"; "p"; "no"]);

  `Check("table loop",
      "
      _t :- _t.
      ",
    "_t", 1, ["no"]);

  `Check("table next",
    "
    _t(X) :- _t(X).
    _t(a).
    ",
  "_t(X)", 2, ["_t(a)"; "no"]);

  `Check("AAMFTESLP",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z), q(Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b).
    q(c).
    ",
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP nodup",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z), q(Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP trclosure order",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,b).
    e(a,d).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP facts order",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", 3, ["_p(a, b)"; "_p(a, c)"; "no"]);

    `Check("AAMFTESLP sld cut",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d) :- !.
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    ",
    "_p(a,Z)", 1, ["no"]);

    `Check("AAMFTESLP sld context",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    x(c).
    ",
    "_p(a,Z), x(Z)", 2, ["_p(a, c), x(c)"; "no"]);

    `Check("AAMFTESLP sld context fail",
    "
    _p(X,Z) :- e(X,Z), q(Z).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    q(a).
    q(b). q(b).
    q(c).
    x(d).
    ",
    "_p(a,Z), x(Z)", 1, ["no"]);

    `Check("fibo",
    "
    f(z).
    f(s(z)).
    f(s(s(X))) :- f(s(X)), f(X).
    ",
    "f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", 1, ["steps"]);

    `Check("fibo tab",
    "
    _f(z).
    _f(s(z)).
    _f(s(s(X))) :- _f(s(X)), _f(X).
    ",
    "_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))", 1, ["_f(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))"]);

    `Check("alternatives to root",
    "
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,Z) :- e(X,Z).
    e(a,d).
    e(a,b).
    e(b,c).
    main(X,Y) :-  _p(X,Y).
    main(a,a).
    main(a,a).
    ",
    "main(a,a)", 3, ["main(a, a)"; "main(a, a)"; "no"]);

    `Check("table trail hard",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", 4, ["_p(a, b)"; "_p(a, c)"; "_p(a, a)"; "no"]);

    `Check("table cut",
    "
    _p(a,b).
    _p(b,c).
    _p(X,Z) :- _p(X,Y), !, _p(Y,Z).
    _p(X,X).
    ",
    "_p(a, X)", 3, ["_p(a, b)"; "_p(a, c)";"no"]);

  ] in

  let filter allowed = function
    | `Check(name,_,_,_,_) -> allowed = [] || List.mem name allowed in
  let checks = List.filter (filter filters) checks in
  List.iter check checks;

  exit !errors
;;


