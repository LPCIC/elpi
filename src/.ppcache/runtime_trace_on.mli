(*a2f05b2efbb3b34e64221a6cf8ecaafd src/runtime_trace_on.mli --cookie elpi_trace="true"*)
#1 "src/runtime_trace_on.mli"
open Util
open Data
module Pp :
sig
  val ppterm :
    ?pp_ctx:pp_ctx ->
      ?min_prec:int ->
        int -> string list -> int -> env -> Format.formatter -> term -> unit
  val uppterm :
    ?pp_ctx:pp_ctx ->
      ?min_prec:int ->
        int -> string list -> int -> env -> Format.formatter -> term -> unit
  val pp_constant : ?pp_ctx:pp_ctx -> Format.formatter -> constant -> unit
  val pp_oref :
    ?pp_ctx:pp_ctx -> Format.formatter -> (UUID.t * Obj.t) -> unit
end
val pp_stuck_goal : ?pp_ctx:pp_ctx -> Fmt.formatter -> stuck_goal -> unit
val embed_query :
  mk_Arg:(State.t -> name:string -> args:term list -> (State.t * term)) ->
    depth:int -> State.t -> 'a Query.t -> (State.t * term)
val execute_once :
  ?max_steps:int ->
    ?delay_outside_fragment:bool -> 'a executable -> 'a outcome
val execute_loop :
  ?delay_outside_fragment:bool ->
    'a executable ->
      more:(unit -> bool) -> pp:(float -> 'a outcome -> unit) -> unit
val deref_uv :
  ?avoid:uvar_body -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv :
  ?avoid:uvar_body ->
    from:constant -> to_:constant -> term list -> term -> term
val deref_head : depth:int -> term -> term
val is_flex : depth:int -> term -> uvar_body option
val expand_uv : depth:int -> uvar_body -> lvl:int -> ano:int -> term
val expand_appuv :
  depth:int -> uvar_body -> lvl:int -> args:term list -> term
val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term
val split_conj : depth:int -> term -> term list
val mkinterval : int -> int -> int -> term list
val mkConst : constant -> term
val mkAppL : constant -> term list -> term
val mkAppArg : int -> int -> term list -> term
val move :
  adepth:int ->
    env -> ?avoid:uvar_body -> from:int -> to_:int -> term -> term
val hmove : ?avoid:uvar_body -> from:int -> to_:int -> term -> term
val subst : depth:int -> term list -> term -> term
val make_index :
  depth:int ->
    indexing:(mode * indexing) Constants.Map.t ->
      (constant * clause) list -> prolog_prog
val get_suspended_goal : 'a stuck_goal_kind -> suspended_goal option
val clausify1 :
  loc:Loc.t ->
    mode Constants.Map.t ->
      nargs:int ->
        depth:int -> term -> ((constant * clause) * clause_src * int)

