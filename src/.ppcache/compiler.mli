(*891155df3b643ea242bbeff13d2aa3f9 src/compiler.mli *)
#1 "src/compiler.mli"
open Util
open Data
type flags = {
  defined_variables: StrSet.t ;
  print_passes: bool }
val default_flags : flags
val compiler_flags : flags State.component
type program
type 'a query
exception CompileError of Loc.t option * string 
type compilation_unit
val init_state : ?symbols_of:State.t -> flags -> State.t
val program_of_ast :
  State.t -> header:compilation_unit -> Ast.Program.t -> (State.t * program)
val unit_of_ast :
  State.t -> ?header:compilation_unit -> Ast.Program.t -> compilation_unit
val assemble_units :
  header:compilation_unit -> compilation_unit list -> (State.t * program)
val extend :
  (State.t * program) -> compilation_unit list -> (State.t * program)
val query_of_ast : State.t -> program -> Ast.Goal.t -> unit query
val query_of_term :
  State.t ->
    program ->
      (depth:int -> State.t -> (State.t * (Loc.t * term))) -> unit query
val query_of_data : State.t -> program -> Loc.t -> 'a Query.t -> 'a query
val optimize_query : 'a query -> 'a executable
val term_of_ast :
  depth:int -> State.t -> (Loc.t * Ast.Term.t) -> (State.t * term)
val pp_query :
  (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) ->
    Format.formatter -> 'a query -> unit
module Symbols :
sig
  val allocate_global_symbol_str : State.t -> string -> (State.t * constant)
end
module Builtins :
sig val register : State.t -> BuiltInPredicate.t -> State.t end
type quotation = depth:int -> State.t -> Loc.t -> string -> (State.t * term)
val set_default_quotation : quotation -> unit
val register_named_quotation : name:string -> quotation -> unit
val lp : quotation
val is_Arg : State.t -> term -> bool
val get_Args : State.t -> term StrMap.t
val mk_Arg : State.t -> name:string -> args:term list -> (State.t * term)
val get_Arg : State.t -> name:string -> args:term list -> term
val quote_syntax :
  [ `Compiletime  | `Runtime of constant -> term ] ->
    State.t -> 'a query -> (State.t * term list * term)
val static_check :
  exec:(unit executable -> unit outcome) ->
    checker:(State.t * program) -> 'a query -> bool
module CustomFunctorCompilation :
sig
  val declare_singlequote_compilation :
    string -> (State.t -> F.t -> (State.t * term)) -> unit
  val declare_backtick_compilation :
    string -> (State.t -> F.t -> (State.t * term)) -> unit
  val compile_singlequote : State.t -> F.t -> (State.t * term)
  val compile_backtick : State.t -> F.t -> (State.t * term)
  val is_singlequote : F.t -> bool
  val is_backtick : F.t -> bool
end

