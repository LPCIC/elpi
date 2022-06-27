(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This file elaborates a traec as spit by the runtime into a list of
   cards to be displayed by the trace browser.
 
   Trace items are first aggregated into steps.
   Then some data is aggregated into steps (like the success of an inference
   based on the success of all siblings, or the text of subgoals when only
   the ID is part of the trace). A stack of rules is also recomputed from the
   father/son link of goals and attached to each card.

   Time stamps are used to preserve the linear time line, that in turn is
   used to nest card traces (e.g. the trace of a CHR guard, or the trace
   of a findall).
  
*)

open Trace_atd
module Str = Re.Str

module Int = struct type t = int let compare x y = x - y end
module Int2 = struct type t = int * int let compare (s1,r1) (s2,r2) = let x = r1 - r2 in if x = 0 then s1 - s2 else x end
module StepMap : Map.S with type key = step_id * runtime_id = Map.Make(Int2)
module GoalMap : Map.S with type key = goal_id = Map.Make(Int)

type time = int
type timestamp = { start : time; stop : time }

(* Reads the raw trace and associates to each item a timestamp *)
module Raw : sig

  val read_stdin : unit -> (timestamp * (item * time) list) StepMap.t

end = struct

(* raw steps *)
let steps : (timestamp * (item * time) list) StepMap.t ref = ref StepMap.empty

let tt = ref 0
let load_item i =
  incr tt;
  if i.kind = [`Info] then
    let { start },items = try StepMap.find (i.step,i.runtime_id) !steps with Not_found -> { start = !tt; stop = !tt },[] in
    steps := StepMap.add (i.step,i.runtime_id) ({ start; stop = !tt }, (i,!tt) :: items) !steps
;;

let read_stdin () =
  let lexer_state = Yojson.Safe.init_lexer () in
  let lexbuf = Lexing.from_channel stdin in
  begin try while true do
    let i = read_item lexer_state lexbuf in
    load_item i
  done
  with Yojson.Json_error _ -> () end;
  !steps

end

(* Elaborated steps, similar to cards but not complete *)
module Elaborate : sig

  module Elaborated_step : sig

    type step_outcode =
      | Success of { siblings : goal_id list}
      | Fail
      
    type attempt = { loc : location; code : string; events : event list }
    type chr_attempt = { loc : location; code: string; events : event list; timestamp : timestamp; removed : goal_id list; resumed : goal_id list;  }
    
    type action =
      | Builtin of { name : builtin_name; outcome : step_outcode; events : event list }
      | Backchain of { trylist : attempt list; outcome : step_outcode }
    
    type step =
      | Inference of { pred : string; goal : string; goal_id : goal_id; action : action; rid : int }
      | Findall of { goal : string; goal_id : goal_id; timestamp : timestamp; result : string list }
      | Cut of  goal_id * (goal_id * location * string) list
      | Suspend of { goal : string; goal_id : goal_id; sibling : goal_id }
      | Resume of (goal_id * string) list
      | CHR of { failed_attempts : chr_attempt list; successful_attempts : chr_attempt list; chr_store_before : (goal_id * goal_text) list; chr_store_after : (goal_id * goal_text) list;}
      | Init of goal_id
    
    type t = timestamp * step

    end
    
  type elaboration = {
    steps : Elaborated_step.t StepMap.t;
    stack_frames : frame list StepMap.t;
    goal_text : string GoalMap.t
  }

  val elaborate : (timestamp * (item * time) list) StepMap.t -> elaboration

  type analysis = {
    aggregated_goal_success : bool GoalMap.t;
    goal_attempts : (step_id * runtime_id) list GoalMap.t
  }

  val success_analysis : Elaborated_step.t StepMap.t -> analysis

end = struct
  module Elaborated_step = struct

    type step_outcode =
      | Success of { siblings : goal_id list}
      | Fail
      
    type attempt = { loc : location; code : string; events : event list }
    type chr_attempt = { loc : location; code: string; events : event list; timestamp : timestamp; removed : goal_id list; resumed : goal_id list;  }
    
    type action =
      | Builtin of { name : builtin_name; outcome : step_outcode; events : event list }
      | Backchain of { trylist : attempt list; outcome : step_outcode }
    
    type step =
      | Inference of { pred : string; goal : string; goal_id : goal_id; action : action; rid : int }
      | Findall of { goal : string; goal_id : goal_id; timestamp : timestamp; result : string list }
      | Cut of goal_id * (goal_id * location * string) list
      | Suspend of { goal : string; goal_id : goal_id; sibling : goal_id }
      | Resume of (goal_id * string) list
      | CHR of { failed_attempts : chr_attempt list; successful_attempts : chr_attempt list; chr_store_before : (goal_id * goal_text) list; chr_store_after : (goal_id * goal_text) list;}
      | Init of goal_id
    
    type t = timestamp * step
    end
    open Elaborated_step

    type elaboration = {
      steps : Elaborated_step.t StepMap.t;
      stack_frames : frame list StepMap.t;
      goal_text : string GoalMap.t
    }

    type analysis = {
    aggregated_goal_success : bool GoalMap.t;
    goal_attempts : (step_id * runtime_id) list GoalMap.t
  }

let elaborated_steps : Elaborated_step.t StepMap.t ref = ref StepMap.empty

(* elaboration *)
let rec filter_map f = function
  | [] -> []
  | x :: xs ->
      match f x with
      | None -> filter_map f xs
      | Some y -> y :: filter_map f xs

let has f l = List.find_opt (fun (i,_) -> i.name = f) l
let all f p l = filter_map (fun (i,_ as it) -> if i.name = f then Some (p it) else None) l
let rec split_on p current = function
  | [] -> (match current with None -> [] | Some x -> [List.rev x])
  |  i :: is when p i ->
    (match current with None -> split_on p (Some [i]) is | Some x -> List.rev x :: split_on p (Some [i]) is)
  | i :: is ->
    split_on p (match current with None -> None | Some x -> Some (i::x)) is
let split_on p l = split_on p None l

let starts_with sl ({ name },_) =
  List.exists (fun s -> Str.(string_match (regexp ("^"^s^".*")) name 0)) sl

let decode_int = function
  | { payload = [ s ] },_ -> int_of_string s
  | _ -> assert false

let decode_string = function
  | { payload }, _ -> String.concat "" payload
let decode_chr_store_entry = function
  | { payload = [ gid; gtext ]}, _ -> int_of_string gid, gtext
  | _ -> assert false

let get s l =
  try (fst @@ List.find (fun ({ name },_) -> name = s) l).payload
  with Not_found -> assert false

type decoded_step =
  [ `Focus of item * time
  | `CHR of (goal_id * goal_text) list * (goal_id * goal_text) list
  | `Resumption of (item * time) list
  | `Init of goal_id
  | `Suspend of item * time
  | `Findall of (item * time) * time
  | `Cut of item * time
  ]

let decode_step l : decoded_step =
  let curgoal = has "user:curgoal" l in
  let rule = has "user:rule" l in
  let builtin = has "user:rule:builtin:name" l in
  let chr = has "user:CHR:try" l in
  let newg = has "user:newgoal" l in
  match curgoal, Option.map decode_string rule, Option.map decode_string builtin, chr, newg with
  | Some g, _, Some "declare_constraint", None, _ -> `Suspend g
  | Some g, Some "findall", _, None, _ -> `Findall (g,snd @@ Option.get rule)
  | Some g, Some "cut", _, None, _ -> `Cut g
  | None, Some "resume", _, None, _ -> `Resumption (List.filter (fun ({ name },_) -> name = "user:rule:resume:resumed") l)
  | None, _, _, Some c, _ -> `CHR (all "user:CHR:store:before" decode_chr_store_entry l, all "user:CHR:store:after" decode_chr_store_entry l)
  | None, _, _, None, Some (x,_) -> `Init (x.goal_id)
  | Some g, _, _, None, _ -> `Focus g
  | _ -> assert false

let decode_attempt = function
  | { payload = [ loc; code ] },_ -> loc, code
  | _ -> assert false

let all_chains f fs l =
  let chains = split_on (fun (i,_) -> i.name = f) l in
  List.map (fun l ->
    List.hd l, 
    List.filter (starts_with fs) (List.tl l)) chains

let all_infer_event_chains f =
  all_chains f ["user:assign";"user:backchain:fail-to"]

let all_chr_event_chains f =
  all_chains f ["user:assign";"user:CHR:rule-failed";"user:CHR:rule-fired";"user:CHR:rule-remove-constraints";"user:subgoal";"user:rule:resume:resumed"]
  
let int_of_string s =
  try int_of_string s
  with Failure _ -> raise (Failure (Printf.sprintf "int_of_string %S" s))

let decode_loc s =
  if Str.(string_match (regexp "File .(context step_id:\\([0-9]+\\))") s 0) then
    `Context (int_of_string (Str.matched_group 1 s))
  else if Str.(string_match (regexp "File .\\([^,]+\\)., line \\([0-9]+\\), column \\([0-9]+\\), character \\([0-9]+\\)") s 0) then
    `File {
      filename = Str.matched_group 1 s;
      line = Str.matched_group 2 s |> int_of_string;
      column = Str.matched_group 3 s |> int_of_string;
      character = Str.matched_group 4 s |> int_of_string;
    }
  else
    (Printf.eprintf "error decoding loc: %s\n" s; exit 1)    

let decode_infer_event ({ name; payload },_ as x) : event =
  match name, payload with
  | "user:assign:resume", [s] -> `ResumeGoal (List.map int_of_string (String.split_on_char ' 's))
  | "user:backchain:fail-to", [s] -> `Fail s
  | _ -> `Assign (decode_string x)

let decode_infer_try (attempt,events) : attempt =
  let loc, code = decode_attempt attempt in
  let events = List.map decode_infer_event events in
  { loc = decode_loc loc; code; events }

let decode_chr_event ( { name; payload; goal_id}, time as x) =
  match name with
  | "user:rule:resume:resumed" -> Some (`CreateGoal goal_id)
  | "user:CHR:rule-remove-constraints" -> Some (`RemoveConstraint (List.map int_of_string payload))
  | "user:assign" -> Some (`Assign (decode_string x))
  | _ -> None

type chr_attempt2 = { loc : location; code : string; events : event list; success : bool; removed: goal_id list; resumed : goal_id list; timestamp : timestamp }
let a2 { loc ; code; events ; success = _; timestamp; removed; resumed} : chr_attempt =
  { loc ; code; events ; timestamp; removed; resumed }

let decode_chr_try ((_,start as attempt),events) : chr_attempt2 =
  let loc, code = decode_attempt attempt in
  let success = has "user:CHR:rule-fired" events <> None in
  let _, stop = List.(hd (rev events)) in
  let events = List.filter_map decode_chr_event events in
  let events, resumed, removed =
    let rec aux a1 a2 a3 = function
      | [] -> List.(rev a1, rev a2, flatten (rev a3))
      | `Assign s :: rest -> aux (`Assign s :: a1) a2 a3 rest
      | `CreateGoal g :: rest -> aux a1 (g :: a2) a3 rest
      | `RemoveConstraint c :: rest -> aux a1 a2 (c :: a3) rest in
    aux [] [] [] events in
  { loc = decode_loc loc; code; events; success; removed; resumed; timestamp = { start; stop } }
  
let decode_chr_try_list l =
  let l = List.map decode_chr_try l in
  let successful_attempts, failed_attempts  = List.partition (fun x -> x.success) l in
  assert(List.length successful_attempts > 0);
  let failed_attempts = List.map a2 failed_attempts in
  let successful_attempts = List.map a2 successful_attempts in
  failed_attempts, successful_attempts

let decode_cut = function
  | { payload = [g;r;t] }, _ -> int_of_string g, decode_loc r, t
  | _ -> assert false

let get_builtin_name l : builtin_name =
  match has "user:rule:builtin:name" l with
  | None -> assert false
  | Some x -> `FFI (decode_string x)

let gstacks : frame list GoalMap.t ref = ref GoalMap.empty (* goal_id -> stack *)
let fstacks : frame list StepMap.t ref = ref StepMap.empty (* step_id -> stack *)

let push_stack (step,rid) goal_id rule siblings =
  let this_stack = try GoalMap.find goal_id !gstacks with Not_found -> [] in
  let stack = { rule; step_id = step; runtime_id = rid } :: this_stack in
  fstacks := StepMap.add (step,rid) stack !fstacks;
  List.iter (fun g -> gstacks := GoalMap.add g stack !gstacks) siblings

let update_stack (step,rid) goal_id rule =
  let old_stack = try GoalMap.find goal_id !gstacks with Not_found -> [] in
  let stack = { rule; step_id = step ; runtime_id = rid} :: old_stack in
  gstacks := GoalMap.add goal_id stack !gstacks


let push_end_stack step goal_id siblings =
  let this_stack = try GoalMap.find goal_id !gstacks with Not_found -> [] in
  let stack = this_stack in
  fstacks := StepMap.add step stack !fstacks;
  assert(siblings=[])
  
let elaborate_step (step,rid) (timestamp,(items : (item * time) list)) : t =
try
  let items = List.rev items in
  let rids = List.map (fun (x,_) -> x.runtime_id) items in
  let rid = List.hd rids in
  assert(List.for_all (fun x -> x = rid) rids);
  timestamp,match decode_step items with
  | `Findall (({ goal_id; payload = [pred;goal] },_),start) ->
      let result = all "user:assign" decode_string items in
      let () = push_stack (step,rid) goal_id (`BuiltinRule (`FFI "findall")) [] in
      let stop =
        match has "user:assign" items with
        | None -> assert false
        | Some (_,time) -> time in
      Findall {goal_id;goal;result;timestamp = { start; stop}}
  | `Suspend ({ goal_id; payload = [pred;goal] },_) ->
       let sibling = all "user:subgoal" decode_int items in
       assert(List.length sibling = 1);
       let () = push_stack (step,rid) goal_id (`BuiltinRule (`Logic "suspend")) sibling in
       Suspend {goal_id;goal;sibling = List.hd sibling} 
  | `Cut ({ goal_id; payload = [pred;goal] },_) ->
      let () = push_stack (step,rid) goal_id (`BuiltinRule (`FFI "!")) [] in
      let cutted = all "user:rule:cut:branch" decode_cut items in
      Cut (goal_id,cutted)
  | `Resumption l ->
      let resumed = List.map (fun ({ goal_id; payload },_ as x) ->
        let () = update_stack (step,rid) goal_id (`BuiltinRule (`Logic "resume")) in
        goal_id, decode_string x) l in
      Resume resumed
  | `CHR(chr_store_before,chr_store_after) ->
    let trylist = all_chr_event_chains "user:CHR:try" items in
    let failed_attempts, successful_attempts = decode_chr_try_list trylist in
    CHR { failed_attempts; successful_attempts; chr_store_before; chr_store_after }
  | `Init g -> Init g
  | `Focus ({ goal_id; payload = [pred;goal] },_) ->
    let action =
      match has "user:rule" items with
      | None | Some ({ payload = [] },_) | Some ({ payload = _ :: _ :: _ },_) -> assert false (* bug in instrumentaion *)
      | Some ({ payload = [ name ] },_) ->
        let siblings = all "user:subgoal" decode_int items in
        let outcome =
          match has ("user:rule:"^name) items with
          | Some ({ payload = [ "success" ] },_) -> Success { siblings }
          | Some ({ payload = [ "fail" ] },_) ->
              (*assert(siblings = []);*)
              Fail
          | _ -> assert false (* bug *) in
        if name = "backchain" then
          let trylist = all_infer_event_chains "user:rule:backchain:try" items in
          let trylist = List.map decode_infer_try trylist in
          if trylist <> [] then begin (* can be empty if the goal is, say, fail *)
            let { loc; code } : attempt = List.hd trylist in
            let () = push_stack (step,rid) goal_id (`UserRule { rule_loc = loc; rule_text = code }) siblings in
            ()
          end else begin
            let () = push_end_stack (step,rid) goal_id siblings in
            ()
          end;
          Backchain { trylist; outcome }
        else if name = "builtin" then
          let name = get_builtin_name items in
          let () = push_stack (step,rid) goal_id (`BuiltinRule name) siblings in
          let events = all_infer_event_chains "user:rule:builtin:name" items in (* ??? *)
          assert(List.length events = 1);
          let _, events = List.hd events in
          Builtin { name; outcome; events = List.map decode_infer_event events  }
        else
          let name = `Logic name in
          let () = push_stack (step,rid) goal_id (`BuiltinRule name) siblings in
          let events = all_infer_event_chains "user:rule:builtin:name" items in (* ??? *)
          let events =
            if events <> [] then snd @@ List.hd events
            else [] in
          Builtin { name; outcome; events = List.map decode_infer_event events  }
     in
     Inference { rid; pred; goal; goal_id; action }

 | _ -> assert false 
with e ->
  let e = Printexc.to_string e in
  raise (Failure (Printf.sprintf "elaborating step %d: %s" step e))

let elaborate (steps : (timestamp * (item * time) list) StepMap.t) =
  let goal_text =
    let goals : string GoalMap.t ref = ref GoalMap.empty in (* goal_id -> goal *)
    StepMap.iter (fun _ (_,is) -> List.iter (fun i ->
      match has "user:newgoal" [i] with
      | None -> ()
      | Some ({ goal_id },_) -> goals := GoalMap.add goal_id (decode_string i) !goals) is) steps;
    !goals in
  let steps : Elaborated_step.t StepMap.t = StepMap.mapi elaborate_step steps in
  { steps; stack_frames = !fstacks; goal_text }

let success_analysis (elaborated_steps : Elaborated_step.t StepMap.t) =

  let aggregated_goal_success =
    let gsuccess : bool GoalMap.t ref = ref GoalMap.empty in (* goal_id -> true = success *)
    let set_success goal_id b =
      gsuccess := GoalMap.add goal_id ((try GoalMap.find goal_id !gsuccess with Not_found -> false) || b) !gsuccess in
    let aggregate_success l =
      List.fold_left (&&) true (List.map (fun x ->
        try GoalMap.find x !gsuccess
        with Not_found -> false) l) in
    StepMap.bindings elaborated_steps |> List.rev |> List.iter (function
      | _, (_,Resume _) -> ()
      | _, (_,Suspend _) -> ()
      | _, (_,Cut _) -> ()
      | _, (_,CHR _) -> ()
      | _, (_,Init _) -> ()
      | _, (_,Findall { goal_id }) -> set_success goal_id true
      | _, (_,Inference { goal_id; action = Builtin { outcome = Fail }}) -> set_success goal_id false 
      | _, (_,Inference { goal_id; action = Builtin { outcome = Success { siblings } }}) -> set_success goal_id (aggregate_success siblings) 
      | _, (_,Inference { goal_id; action = Backchain { outcome = Fail }}) -> set_success goal_id false 
      | _, (_,Inference { goal_id; action = Backchain { outcome = Success { siblings } }}) -> set_success goal_id (aggregate_success siblings) 
    );
    !gsuccess in

  let goal_attempts =
    let gattempts : (step_id * runtime_id) list GoalMap.t ref = ref GoalMap.empty in (* goal_id -> true = success *)
    let add_more_success goal_id step_id =
      try
        let l = GoalMap.find goal_id !gattempts in
        gattempts := GoalMap.add goal_id (step_id :: l) !gattempts
      with Not_found ->
        gattempts := GoalMap.add goal_id [step_id] !gattempts
      in
    StepMap.bindings elaborated_steps |> List.iter (function
    | _, (_,Resume _) -> ()
    | _, (_,Suspend _) -> ()
    | _, (_,Findall _) -> ()
    | _, (_,Cut _) -> ()
    | _, (_,CHR _) -> ()
    | _, (_,Init _) -> ()
    | _, (_,Inference { action = Builtin _}) -> ()
    | _, (_,Inference { action = Backchain { outcome = Fail }}) -> ()
    | step_id, (_,Inference { goal_id; action = Backchain { outcome = Success _ }}) ->
        add_more_success goal_id step_id
    );
    !gattempts in

  { aggregated_goal_success; goal_attempts }

end    
    
(* Aggrgates some data computed by Elaborate and structures sub-traces *)
module Trace : sig

  val cards :
    Elaborate.Elaborated_step.t StepMap.t ->
    stack_frames:frame list StepMap.t ->
    aggregated_goal_success:bool GoalMap.t ->
    goal_text:string GoalMap.t ->
    goal_attempts:(step_id * runtime_id) list GoalMap.t ->
      trace

end = struct

  open Elaborate.Elaborated_step

  let find_success goal_success x =
    try GoalMap.find x goal_success
    with Not_found -> false
  
  let find_goal_text  goal_goal_text  x =
    try GoalMap.find x goal_goal_text 
    with Not_found -> raise (Failure (Printf.sprintf "find_goal_text  %d not found" x))
 

  let cards elaborated_steps ~stack_frames ~aggregated_goal_success ~goal_text ~goal_attempts : trace =
    let find_success = find_success aggregated_goal_success in
    let find_goal_text = find_goal_text goal_text in
    let pre_cards =
    StepMap.bindings elaborated_steps |> List.map (fun ((step_id,runtime_id),(timestamp,step)) ->
      let step =
        match step with
        | Inference { rid; goal; pred; goal_id; action } ->
             let stack =
               try StepMap.find (step_id,runtime_id) stack_frames
               with Not_found -> assert false in
             let failed_attempts, successful_attempts =
               match action with
               | Builtin { name; outcome = Fail; events } ->
                  [{ rule = `BuiltinRule name ; events}],[]
               | Builtin { name; outcome = Success { siblings }; events } ->
                  let siblings_aggregated_outcome =
                    if List.fold_left (&&) true (List.map find_success siblings) then `Success else `Fail in
                  let siblings = List.map (fun goal_id -> { goal_id; goal_text = find_goal_text goal_id }) siblings in
                  [],[{ attempt = { rule = `BuiltinRule name; events}; siblings; siblings_aggregated_outcome }]
               | Backchain { trylist ; outcome = Fail } ->
                  List.map (fun ({ loc; code; events } : attempt) -> { rule = `UserRule { rule_text = code; rule_loc = loc } ; events } ) trylist,[]
               | Backchain { trylist ; outcome = Success { siblings } } ->
                  let faillist = List.tl trylist in
                  let { loc; code; events } : attempt = List.hd trylist in
                  List.map (fun ({ loc; code; events } : attempt) -> { rule = `UserRule { rule_text = code; rule_loc = loc } ; events } ) faillist,
                  let siblings_aggregated_outcome =
                    if List.fold_left (&&) true (List.map find_success siblings) then `Success else `Fail in
                  let siblings = List.map (fun goal_id -> { goal_id; goal_text = find_goal_text goal_id }) siblings in
                  [{attempt = { rule = `UserRule { rule_loc = loc; rule_text = code }; events}; siblings; siblings_aggregated_outcome}]  
             in
             let more_successful_attempts =
               try
                 GoalMap.find goal_id goal_attempts |>
                 List.filter (fun (s,r) -> r = runtime_id && s > step_id) |>
                 List.map fst |>
                 List.sort Stdlib.compare
               with
                 Not_found -> [] in
             let inference = {
               current_goal_id = goal_id;
               current_goal_text = goal;
               current_goal_predicate = pred;
               failed_attempts;
               successful_attempts;
               more_successful_attempts;
               stack;
             } in
             assert(runtime_id = rid);
             `Inference inference
        | Resume l ->
          `Resume (List.map (fun (goal_id,goal_text) -> { goal_id; goal_text }) l)
        | Suspend { goal; goal_id; sibling } ->
          let stack =
            try StepMap.find (step_id,runtime_id) stack_frames
            with Not_found -> assert false in
          `Suspend {
             suspend_goal_id = goal_id;
             suspend_goal_text = goal;
             suspend_sibling = { goal_id = sibling; goal_text = find_goal_text sibling };
             suspend_stack = stack;
            } 
        | Cut (goal_id,l) -> `Cut (goal_id,l |> List.map (fun (g,rule_loc,rule_text) -> { cut_branch_for_goal = { goal_id = g; goal_text = find_goal_text g }; cut_branch = { rule_text; rule_loc }}))
        | Findall { goal; goal_id; timestamp; result } ->
            `Findall_TODO ( goal, goal_id, timestamp, result)
        | CHR { failed_attempts; successful_attempts; chr_store_before; chr_store_after } ->
            let chr_store_before = chr_store_before |> List.map (fun (goal_id,goal_text) -> { goal_id; goal_text }) in
            let chr_store_after = chr_store_after |> List.map (fun (goal_id,goal_text) -> { goal_id; goal_text }) in
            `CHR_TODO (failed_attempts,successful_attempts,chr_store_before, chr_store_after)
        | Init goal_id -> `Init { goal_id; goal_text = find_goal_text goal_id }
      in
      timestamp,(step,step_id,runtime_id)) in
      (* bad complexity *)
      let in_time_stamp { start; stop } { start = start1; stop = stop1 } = start1 >= start && stop1 <= stop in
      let rec to_chr_attempt ( x : chr_attempt) : Trace_atd.chr_attempt =
        let chr_loc = match x.loc with `File x -> x | `Context _ -> assert false in
        let chr_text = x.code in
        let chr_condition_cards : card list =
          pre_cards |> List.filter (fun (time,_) -> in_time_stamp x.timestamp time)
          |> List.map pre_card2card in
        assert(
          let rid = (List.hd chr_condition_cards).runtime_id in
          List.for_all (fun ({ runtime_id } : card) -> runtime_id = rid) chr_condition_cards);
        { Trace_atd.chr_loc; chr_text; chr_condition_cards }

      and to_successful_chr_attempt ( x : chr_attempt) : successful_chr_attempt =
        let chr_loc = match x.loc with `File x -> x | `Context _ -> assert false in
        let chr_text = x.code in
        let chr_condition_cards : card list =
          pre_cards |> List.filter (fun (time,_) -> in_time_stamp x.timestamp time)
          |> List.map pre_card2card in
        assert(
          let rid = (List.hd chr_condition_cards).runtime_id in
          List.for_all (fun ({ runtime_id } : card) -> runtime_id = rid) chr_condition_cards);
        let chr_new_goals = List.map (fun goal_id -> { goal_id; goal_text = find_goal_text goal_id }) x.resumed in
        { chr_attempt = { chr_loc; chr_text; chr_condition_cards }; chr_new_goals; chr_removed_goals = x.removed }
          
      and inference_color rid { successful_attempts; more_successful_attempts } =
        match successful_attempts, List.rev more_successful_attempts with
        | [], [] -> `Red
        | [], _ :: _ -> assert false
        | [ { siblings_aggregated_outcome = `Success }], [] -> `Green
        | [ { siblings_aggregated_outcome = `Success }], _ :: _ -> `YellowGreen
        | [ { siblings_aggregated_outcome = `Fail }], [] -> `Red
        | [ { siblings_aggregated_outcome = `Fail }], last :: _ ->
              let (_,(step,_,_)) = List.find (fun (_,(_,step_id,runtime_id)) -> runtime_id = rid && step_id = last) pre_cards in
              begin match step with
              | `Inference x ->
                  begin match inference_color rid x with
                  | `Green -> `YellowGreen
                  | `Red -> `YellowRed
                  | x -> x
                  end
              | _ -> assert false
              end
        | _ -> assert false
          
      and  pre_card2card (_,(step,step_id,runtime_id)) =
        match step with
        | `Init g -> { step_id; step = `Init g; runtime_id; color = `Grey }
        | `Resume x -> { step_id; step = `Resume x; runtime_id; color = `Grey }
        | `Inference x -> { step_id; step = `Inference x; runtime_id; color = inference_color runtime_id x }
        | `CHR_TODO (failed_attempts,successful_attempts,chr_store_before, chr_store_after) ->
          let chr_failed_attempts = List.map to_chr_attempt failed_attempts in
          let chr_successful_attempts = List.map to_successful_chr_attempt successful_attempts in
          let step = `CHR { chr_failed_attempts; chr_successful_attempts; chr_store_before; chr_store_after} in
          { step_id; step; runtime_id; color = `Grey }
        | `Findall_TODO ( goal, goal_id, timestamp, result) ->
          let findall_cards =
            pre_cards |> List.filter (fun (time,_) -> in_time_stamp timestamp time) in
          let findall_cards = findall_cards |> List.map pre_card2card in
          assert(
            let rid = (List.hd findall_cards).runtime_id in
            List.for_all (fun ({ runtime_id } : card) -> runtime_id = rid) findall_cards);
          let stack =
            try StepMap.find (step_id,runtime_id) stack_frames
            with Not_found -> assert false in
          let findall = {
            findall_goal_id = goal_id;
            findall_goal_text = goal;
            findall_cards;
            findall_solution_text = result;
            findall_stack = stack } in
          { step_id; step = `Findall findall; runtime_id; color = `Green }
        | `Suspend x -> { step_id; step = `Suspend x; runtime_id; color = `Grey }
        | `Cut (cut_goal_id,cut_victims) ->
             { step_id; step = `Cut { cut_goal_id; cut_victims }; runtime_id; color = `Grey }
      in

      let min_rid = List.fold_left (fun acc (_,(_,_,rid)) -> min acc rid) max_int pre_cards in
      pre_cards |> List.filter (fun (_,(_,_,rid)) -> rid = min_rid) |> List.map pre_card2card
      
end

let main =
  let raw_steps = Raw.read_stdin () in

  let { Elaborate.steps;  stack_frames; goal_text } = Elaborate.elaborate raw_steps in
  let { Elaborate.aggregated_goal_success; goal_attempts } = Elaborate.success_analysis steps in

  let cards = Trace.cards steps ~stack_frames ~aggregated_goal_success ~goal_text ~goal_attempts in

  let ob = Bi_outbuf.create_channel_writer stdout in
  write_trace ob cards;
  Bi_outbuf.flush_channel_writer ob
