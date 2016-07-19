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

exception Error of string Lazy.t

type goal = int

(** {2 Goal stack} *)

module Stack:
sig
  type switch = Open of goal | Closed of goal
  type locator = int * switch
  type tag = [ `BranchTag | `FocusTag | `NoTag ]
  type entry = locator list * locator list * locator list * tag
  type t = entry list

  val empty: t

  val find_goal: t -> goal            (** find "next" goal *)
  val is_empty: t -> bool             (** a singleton empty level *)
  val of_nmetasenv: (goal * 'a) list -> t
  val head_switches: t -> switch list (** top level switches *)
  val head_goals: t -> goal list      (** top level goals *)
  val head_tag: t -> tag              (** top level tag *)
  val shift_goals: t -> goal list     (** second level goals *)
  val open_goals: t -> goal list      (** all (Open) goals *)
  val goal_of_switch: switch -> goal
  val filter_open : (goal * switch) list -> (goal * switch) list
  val is_open: goal * switch -> bool
  val is_fresh: goal * switch -> bool
  val init_pos: (goal * switch) list -> (goal * switch) list 
  val goal_of_loc: goal * switch -> goal
  val switch_of_loc: goal * switch -> switch
  val zero_pos : goal list -> (goal * switch) list
  val deep_close: goal list -> t -> t


  val ( @+ ) : 'a list -> 'a list -> 'a list
  val ( @- ) : 'a list -> 'a list -> 'a list
  val ( @~- ) : ('a * switch) list -> goal list -> ('a * switch) list



  (** @param int depth, depth 0 is the top of the stack *)
  val fold:
    env: ('a -> int -> tag -> locator -> 'a) ->
    cont:('a -> int -> tag -> locator -> 'a) ->
    todo:('a -> int -> tag -> locator -> 'a) ->
      'a  -> t -> 'a

  val iter: (** @param depth as above *)
    env: (int -> tag -> locator -> unit) ->
    cont:(int -> tag -> locator -> unit) ->
    todo:(int -> tag -> locator -> unit) ->
      t -> unit

  val map:  (** @param depth as above *)
    env: (int -> tag -> locator list -> locator list) ->
    cont:(int -> tag -> locator list -> locator list) ->
    todo:(int -> tag -> locator list -> locator list) ->
      t -> t

  val pp: t -> string
end

(** {2 Functorial interface} *)

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

module Make (S: Status) : C
  with type tactic = S.tactic
   and type input_status = S.input_status
   and type output_status = S.output_status

