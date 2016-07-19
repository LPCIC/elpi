(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id: continuationals.ml 10987 2010-10-08 13:21:54Z asperti $ *)

open Printf

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

exception Error of string lazy_t
let fail msg = raise (Error msg)

type goal = int

module Stack =
struct
  type switch = Open of goal | Closed of goal
  type locator = int * switch
  type tag = [ `BranchTag | `FocusTag | `NoTag ]
  type entry = locator list * locator list * locator list * tag
  type t = entry list

  let empty = [ [], [], [], `NoTag ]

  let fold ~env ~cont ~todo init stack =
    let rec aux acc depth =
      function
      | [] -> acc
      | (locs, todos, conts, tag) :: tl ->
          let acc = List.fold_left (fun acc -> env acc depth tag)  acc locs in
          let acc = List.fold_left (fun acc -> cont acc depth tag) acc conts in
          let acc = List.fold_left (fun acc -> todo acc depth tag) acc todos in
          aux acc (depth + 1) tl
    in
    assert (stack <> []);
    aux init 0 stack

  let iter ~env ~cont ~todo =
    fold ~env:(fun _ -> env) ~cont:(fun _ -> cont) ~todo:(fun _ -> todo) ()

  let map ~env ~cont ~todo =
    let depth = ref ~-1 in
    List.map
      (fun (s, t, c, tag) ->
        incr depth;
        let d = !depth in
        env d tag s, todo d tag t, cont d tag c, tag)

  let is_open = function _, Open _ -> true | _ -> false
  let close = function n, Open g -> n, Closed g | l -> l
  let filter_open = List.filter is_open
  let is_fresh = 
    function n, Open _ when n > 0 -> true | _,Closed _ -> true | _ -> false
  let goal_of_loc = function _, Open g | _, Closed g -> g
  let goal_of_switch = function Open g | Closed g -> g
  let switch_of_loc = snd

  let zero_pos = List.map (fun g -> 0, Open g)

  let init_pos locs =
    let pos = ref 0 in  (* positions are 1-based *)
    List.map (function _, sw -> incr pos; !pos, sw) locs

  let extract_pos i =
    let rec aux acc =
      function
      | [] -> fail (lazy (sprintf "relative position %d not found" i))
      | (i', _) as loc :: tl when i = i' -> loc, (List.rev acc) @ tl
      | hd :: tl -> aux (hd :: acc) tl
    in
    aux []

  let deep_close gs =
    let close _ _ =
      List.map (fun l -> if List.mem (goal_of_loc l) gs then close l else l)
    in
    let rm _ _ = List.filter (fun l -> not (List.mem (goal_of_loc l) gs)) in
    map ~env:close ~cont:rm ~todo:rm

  let rec find_goal =
    function
    | [] -> raise (Failure "Continuationals.find_goal")
    | (l :: _,   _   ,   _   , _) :: _ -> goal_of_loc l
    | (  _   ,   _   , l :: _, _) :: _ -> goal_of_loc l
    | (  _   , l :: _,   _   , _) :: _ -> goal_of_loc l
    | _ :: tl -> find_goal tl

  let is_empty =
    function
    | [] -> assert false
    | [ [], [], [], `NoTag ] -> true
    | _ -> false

  let of_nmetasenv metasenv =
    let goals = List.map (fun (g, _) -> g) metasenv in
    [ zero_pos goals, [], [], `NoTag ]

  let head_switches =
    function
    | (locs, _, _, _) :: _ -> List.map switch_of_loc locs
    | [] -> assert false

  let head_goals =
    function
    | (locs, _, _, _) :: _ -> List.map goal_of_loc locs
    | [] -> assert false

  let head_tag =
    function
    | (_, _, _, tag) :: _ -> tag
    | [] -> assert false

  let shift_goals =
    function
    | _ :: (locs, _, _, _) :: _ -> List.map goal_of_loc locs
    | [] -> assert false
    | _ -> []

  let open_goals stack =
    let add_open acc _ _ l = if is_open l then goal_of_loc l :: acc else acc in
    List.rev (fold ~env:add_open ~cont:add_open ~todo:add_open [] stack)

  let (@+) = (@)  (* union *)

  let (@-) s1 s2 =  (* difference *)
    List.fold_right
      (fun e acc -> if List.mem e s2 then acc else e :: acc)
      s1 []

  let (@~-) locs gs = (* remove some goals from a locators list *)
    List.fold_right
      (fun loc acc -> if List.mem (goal_of_loc loc) gs then acc else loc :: acc)
      locs []

  let pp stack =
    let pp_goal = string_of_int in
    let pp_switch =
      function Open g -> "o" ^ pp_goal g | Closed g -> "c" ^ pp_goal g
    in
    let pp_loc (i, s) = string_of_int i ^ pp_switch s in
    let pp_env env = sprintf "[%s]" (String.concat ";" (List.map pp_loc env)) in
    let pp_tag = function `BranchTag -> "B" | `FocusTag -> "F" | `NoTag -> "N" in
    let pp_stack_entry (env, todo, cont, tag) =
      sprintf "(%s, %s, %s, %s)" (pp_env env) (pp_env todo) (pp_env cont)
        (pp_tag tag)
    in
    String.concat " :: " (List.map pp_stack_entry stack)
end

module type Status =
sig
  type input_status
  type output_status

  type tactic
  val mk_tactic : (input_status -> output_status) -> tactic
  val apply_tactic : tactic -> input_status -> output_status

  val goals : output_status -> goal list * goal list (** opened, closed goals *)
  val get_stack : input_status -> Stack.t
  val set_stack : Stack.t -> output_status -> output_status

  val inject : input_status -> output_status
  val focus : goal -> output_status -> input_status
end

module type C =
sig
  type input_status
  type output_status
  type tactic

  type tactical =
    | Tactic of tactic
    | Skip

  type t =
    | Dot
    | Semicolon

    | Branch
    | Shift
    | Pos of int list
    | Wildcard
    | Merge

    | Focus of goal list
    | Unfocus

    | Tactical of tactical

  val eval: t -> input_status -> output_status
end

module Make (S: Status) =
struct
  open Stack

  type input_status = S.input_status
  type output_status = S.output_status
  type tactic = S.tactic

  type tactical =
    | Tactic of tactic
    | Skip

  type t =
    | Dot
    | Semicolon
    | Branch
    | Shift
    | Pos of int list
    | Wildcard
    | Merge
    | Focus of goal list
    | Unfocus
    | Tactical of tactical

  let pp_t =
    function
    | Dot -> "Dot"
    | Semicolon -> "Semicolon"
    | Branch -> "Branch"
    | Shift -> "Shift"
    | Pos i -> "Pos " ^ (String.concat "," (List.map string_of_int i))
    | Wildcard -> "Wildcard"
    | Merge -> "Merge"
    | Focus gs ->
        sprintf "Focus [%s]" (String.concat "; " (List.map string_of_int gs))
    | Unfocus -> "Unfocus"
    | Tactical _ -> "Tactical <abs>"

  let eval_tactical tactical ostatus switch =
    match tactical, switch with
    | Tactic tac, Open n ->
        let ostatus = S.apply_tactic tac (S.focus n ostatus) in
        let opened, closed = S.goals ostatus in
        ostatus, opened, closed
    | Skip, Closed n -> ostatus, [], [n]
    | Tactic _, Closed _ -> fail (lazy "can't apply tactic to a closed goal")
    | Skip, Open _ -> fail (lazy "can't skip an open goal")

  let eval cmd istatus =
    let stack = S.get_stack istatus in
    debug_print (lazy (sprintf "EVAL CONT %s <- %s" (pp_t cmd) (pp stack)));
    let new_stack stack = S.inject istatus, stack in
    let ostatus, stack =
      match cmd, stack with
      | _, [] -> assert false
      | Tactical tac, (g, t, k, tag) :: s ->
(* COMMENTED OUT TO ALLOW PARAMODULATION TO DO A 
 *   auto paramodulation.try assumption.
 * EVEN IF NO GOALS ARE LEFT OPEN BY AUTO.
  
  if g = [] then fail (lazy "can't apply a tactic to zero goals");
  
*)
          debug_print (lazy ("context length " ^string_of_int (List.length g)));
          let rec aux s go gc =
            function
            | [] -> s, go, gc
            | loc :: loc_tl ->
                debug_print (lazy "inner eval tactical");
                let s, go, gc =
                  if List.exists ((=) (goal_of_loc loc)) gc then
                    s, go, gc
                  else
                    let s, go', gc' = eval_tactical tac s (switch_of_loc loc) in
                    s, (go @- gc') @+ go', gc @+ gc'
                in
                aux s go gc loc_tl
          in
          let s0, go0, gc0 = S.inject istatus, [], [] in
          let sn, gon, gcn = aux s0 go0 gc0 g in
          debug_print (lazy ("opened: "
            ^ String.concat " " (List.map string_of_int gon)));
          debug_print (lazy ("closed: "
            ^ String.concat " " (List.map string_of_int gcn)));
          let stack =
            (zero_pos gon, t @~- gcn, k @~- gcn, tag) :: deep_close gcn s
          in
          sn, stack
      | Dot, ([], _, [], _) :: _ ->
          (* backward compatibility: do-nothing-dot *)
          new_stack stack
      | Dot, (g, t, k, tag) :: s ->
          (match filter_open g, k with
          | loc :: loc_tl, _ -> new_stack (([ loc ], t, loc_tl @+ k, tag) :: s)
          | [], loc :: k ->
              assert (is_open loc);
              new_stack (([ loc ], t, k, tag) :: s)
          | _ -> fail (lazy "can't use \".\" here"))
      | Semicolon, _ -> new_stack stack
      | Branch, (g, t, k, tag) :: s ->
          (match init_pos g with
          | [] | [ _ ] -> fail (lazy "too few goals to branch");
          | loc :: loc_tl ->
              new_stack
                (([ loc ], [], [], `BranchTag) :: (loc_tl, t, k, tag) :: s))
      | Shift, (g, t, k, `BranchTag) :: (g', t', k', tag) :: s ->
          (match g' with
          | [] -> fail (lazy "no more goals to shift")
          | loc :: loc_tl ->
              new_stack
                (([ loc ], t @+ filter_open g @+ k, [],`BranchTag)
                :: (loc_tl, t', k', tag) :: s))
      | Shift, _ -> fail (lazy "can't shift goals here")
      | Pos i_s, ([ loc ], t, [],`BranchTag) :: (g', t', k', tag) :: s
        when is_fresh loc ->
          let l_js = List.filter (fun (i, _) -> List.mem i i_s) ([loc] @+ g') in
          new_stack
            ((l_js, t , [],`BranchTag)
             :: (([ loc ] @+ g') @- l_js, t', k', tag) :: s)
      | Pos _, _ -> fail (lazy "can't use relative positioning here")
      | Wildcard, ([ loc ] , t, [], `BranchTag) :: (g', t', k', tag) :: s
          when is_fresh loc ->
            new_stack
              (([loc] @+ g', t, [], `BranchTag)
                :: ([], t', k', tag) :: s)
      | Wildcard, _ -> fail (lazy "can't use wildcard here")
      | Merge, (g, t, k,`BranchTag) :: (g', t', k', tag) :: s ->
          new_stack ((t @+ filter_open g @+ g' @+ k, t', k', tag) :: s)
      | Merge, _ -> fail (lazy "can't merge goals here")
      | Focus [], _ -> assert false
      | Focus gs, s ->
          let stack_locs =
            let add_l acc _ _ l = if is_open l then l :: acc else acc in
            Stack.fold ~env:add_l ~cont:add_l ~todo:add_l [] s
          in
          List.iter
            (fun g ->
              if not (List.exists (fun l -> goal_of_loc l = g) stack_locs) then
                fail (lazy (sprintf "goal %d not found (or closed)" g)))
            gs;
          new_stack ((zero_pos gs, [], [], `FocusTag) :: deep_close gs s)
      | Unfocus, ([], [], [], `FocusTag) :: s -> new_stack s
      | Unfocus, _ -> fail (lazy "can't unfocus, some goals are still open")
    in
    debug_print (lazy (sprintf "EVAL CONT %s -> %s" (pp_t cmd) (pp stack)));
    S.set_stack stack ostatus
end

