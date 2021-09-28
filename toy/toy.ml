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
let trail = ref []

let assign v t =
  trail := v :: !trail;
  [%spy "assign" ~rid pp_tm (Var v)];
  [%spy "assign:with" ~rid pp_tm t];
  v := t

let rec backtrack o =
  if o != !trail then begin
    match !trail with
    | [] -> assert false
    | v :: vs ->
        v := dummy;
        trail := vs;
        backtrack o
  end

let rec chop_trail o trail =
  if o != trail then
    match trail with
    | [] -> assert false
    | v :: vs -> v :: chop_trail o vs
  else
     []
let chop_trail o = chop_trail o !trail


type goal = tm
[@@deriving show]

type rule = int * tm * tm list
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

let rec unif (s:tm array) (a:tm) (b:tm) = match a, b with
  (* deref *)
  | Var r, _ when !r != dummy -> unif s !r b
  | _, Var r when !r != dummy -> unif s a !r
  | _, Arg i when s.(i) != dummy -> unif s a s.(i)
  | Arg _, _ -> assert false

  (* assign *)
  | Var r, _ -> assign r (heapify s b); true
  | _, Var r -> assign r a; true (* missing OC *)
  | _, Arg i -> s.(i) <- a; true

  | App(c1,args1), App(c2,args2) ->
    if c1 <> c2 then false
    else fold_left2 (unif s) args1 args2

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

let rec canonify i (g : tm) : int * canonical_goal =
  match g with
  | Arg _ -> assert false
  | Var r when !r <> dummy -> canonify i !r
  | Var r -> assign r canonical_names.(i); i+1, !r
  | App(s,args) ->
      let i, args = map_acc canonify i args in
      i, App(s,args)

let copy g =
  let old_trail = !trail in
  let n, _ = canonify 0 g in
  backtrack old_trail;
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
  let old_trail = !trail in
  let _, g = canonify 0 g in
  backtrack old_trail;
  g

(* we could canonify g and then Stdlib.compare (OC can be expensive)*)
let variant (c : canonical_goal) (g : goal) =
  let old_trail = !trail in
  let u = unif [||] g c in (* pass g on the left to avoid heapify on assign *)
  backtrack old_trail;
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
and alt = {
  goal: goal;
  rules : rule list; [@printer (fun _ _ -> ())]
  stack : frame; [@printer (fun _ _ -> ())]
  old_trail : tm ref list; [@printer (fun _ _ -> ())]
  cutinfo : alt list; [@printer (fun _ _ -> ())]
}

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

let pp_alts fmt l = Format.fprintf fmt "%d" (List.length l)
    
let all_rules = ref []
let gas = ref 0

let tabled = function
  | App(s,_) -> s.[0] = '_'
  | _ -> false

type table_entry_status = Incomplete | Complete

let table = ref DT.empty

let rec select goal = function
  | [] -> None
  | (stack,hd,conds)::rules ->
    let old_trail = !trail in
    let stack = Array.init stack (fun _ -> dummy) in
    if not (unif stack goal hd) then begin
      backtrack old_trail;
      select goal rules
    end else begin
      [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a /// %a :- %a." pp_tm goal pp_tm hd pp_tm (App("&",conds))) ()];
      Some (List.map (heapify stack) conds, rules)
    end

let new_table_entry cgoal =
  table := DT.add cgoal ([],Incomplete) !table

type consumer = {
  next : frame;
  goal : tm;
}
[@@deriving show]

type generator = {
  next : frame;
  goal : tm;
  rules : rule list; [@printer (fun fmt l -> Format.fprintf fmt "%d" (List.length l))]
  undo : tm ref list;
}
[@@deriving show]

type slg_status = {
  consumers : consumer list DT.t; [@printer (fun _ _ -> ())]
  generators : generator list;
  resume_queue : (consumer * rule) list;
}
[@@deriving show]

let empty_slg_status = {
  consumers = DT.empty;
  generators = [];
  resume_queue = [];
}

type sld_status = {
  goal : goal;
  rules : rule list;
  next : frame;
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

let rec run { goal; rules; next; alts; cutinfo } (sgs : slg_status) =
  [%trace "run" ~rid 
    ("@[<hov 2>g: %a@ next: %a@ alts: %a@]@\n" pp_tm goal pp_frame next pp_alts alts)
  begin match !gas with
  | 0 -> `TIMEOUT
  | _ ->
    decr gas;
    if tabled goal then enter_slg goal rules next alts cutinfo sgs
    else sld goal rules next alts cutinfo sgs
end]

and enter_slg goal rules next alts cutinfo sgs =
  let cgoal = canonify goal in
  match DT.find cgoal !table with
  | [], Incomplete ->
      [%spy "slg:suspend" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next } sgs in
      advance_slg sgs
  | answers, Complete ->
      [%spy "slg:complete->sld" ~rid pp_tm cgoal];
      sld goal answers next alts cutinfo sgs
  | answers, Incomplete ->
      [%spy "slg:incomplete->sld+slg" ~rid pp_tm cgoal];
      let sgs = push_consumer cgoal { goal; next } sgs in
      sld goal answers next alts cutinfo sgs
  | exception Not_found ->
      [%spy "slg:new" ~rid pp_tm cgoal];
      new_table_entry cgoal;
      let sgs = push_consumer cgoal { goal; next = Root(next,alts) } sgs in
      let goal = copy goal in (* also copy the program *)
      let sgs = push_generator { undo = []; goal; rules; next = Contribute(goal,cgoal) } sgs in
      advance_slg sgs

and advance_slg ({ generators; resume_queue; _ } as s) =
  [%trace "slg:step" ~rid ("@[<hov 2>%a]@\n" pp_slg_status s)
  begin match resume_queue with
  | ({goal ; next }, solution) :: resume_queue ->
      let s = { s with resume_queue } in
      (*let old_trail = !trail in*)
      begin match select goal [solution] with
      | None -> advance_slg s
      | Some([],[]) -> pop_andl next [] s
      | _ -> assert false (* solutions have no subgoals *)
      end
  | [] ->
     match generators with
     | [] -> `FAIL (* TODO backtrack on the alternativbes of the root *)
     | { rules = []; next = Contribute(_,cgoal); _ } :: generators ->
          table_entry_complete cgoal;
          advance_slg { s with generators }
     | { rules = []; _ } :: generators -> advance_slg { s with generators }
     | { undo; goal; next; rules } :: generators ->
        List.iter (fun x -> x := dummy) undo;
        let old_trail = !trail in
        match select goal rules with
        | None -> advance_slg { s with generators }
        | Some ([], rules) ->
            let s = { s with generators = { undo = chop_trail old_trail; goal; next; rules } :: generators } in
            pop_andl next [] s
        | Some (ngoal::brothers, rules) ->
            let s = { s with generators = { undo = chop_trail old_trail; goal; next; rules } :: generators } in
            let next = Todo { brothers; cutinfo = []; siblings = next } in
            run { goal = ngoal; next; alts = []; rules = !all_rules; cutinfo = [] } s        
  end]

and sld goal rules next (alts : alts) (cutinfo : alts) (sgs : slg_status) =
  if goal = cut then pop_andl next cutinfo sgs
  else 
    let old_trail = !trail in
    match select goal rules with
    | None -> next_alt alts sgs
    | Some ([], []) -> pop_andl next alts sgs
    | Some ([], rules) ->
        let alts = { goal; rules; stack=next; old_trail; cutinfo } :: alts in
        pop_andl next alts sgs
    | Some (goal :: rest, rules) ->
        let old_alts = alts in
        let alts = { goal; rules; stack=next; old_trail; cutinfo } :: alts in
        let next = Todo { brothers = rest; cutinfo; siblings = next } in
        run { goal; rules = !all_rules; next; alts; cutinfo = old_alts } sgs

and pop_andl next alts sgs =
  match next with
  | Done -> `OK (alts,sgs)
  | Root(next, alts) -> pop_andl next alts sgs
  | Contribute(solution,cgoal) ->
      let sgs = table_solution cgoal solution sgs in
      advance_slg sgs
  | Todo { brothers = []; siblings = next; _ } -> pop_andl next alts sgs
  | Todo { brothers = goal :: brothers; cutinfo; siblings } ->
      run { goal; rules = !all_rules;
            next = Todo { brothers = brothers; cutinfo; siblings };
            alts; cutinfo } sgs
            
and next_alt alts sgs = match alts with
  | [] -> (*`FAIL (* TODO: do slg *)*) advance_slg sgs
  | { goal; rules; stack=next; old_trail; cutinfo } :: alts ->
      backtrack old_trail;
      run { goal; rules; next; alts; cutinfo } sgs

let run goal rules =
  match goal with
  | [] -> assert false
  | [goal] -> run { goal; rules; next = Done; alts = []; cutinfo = [] } empty_slg_status
  | goal::gs -> run { goal; rules; next = Todo { brothers = gs; siblings = Done; cutinfo = []}; alts = []; cutinfo = [] } empty_slg_status

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
  let rec all n = function
  | `FAIL -> [Format.asprintf "no"]
  | `TIMEOUT -> [Format.asprintf "steps"]
  | `OK (alts,sgs) ->
      let s = Format.asprintf "%a" (ppl ", ") query in
      if n = 1 then [s]
      else s :: all (n-1) (next_alt alts sgs)
  in
  all n (run query !all_rules)

let errors = ref 0
let check ?(steps=100) (`Check(s,p,q,n,l1)) =
  let l2 = main q steps n p in
  if l1 <> l2 then begin
    incr errors;
    Format.eprintf "ERROR: %s:\n%a\n%a\n%!" s
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l1
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l2
  end else
    Format.eprintf "%s: ok\n%!" s

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
    "_p(a,Z)", 2, ["_p(a, b)"; "_p(a, c)"; "no"]);

  ] in

  let filter allowed = function
    | `Check(name,_,_,_,_) -> allowed = [] || List.mem name allowed in
  let checks = List.filter (filter filters) checks in
  List.iter check checks;

  exit !errors
;;


