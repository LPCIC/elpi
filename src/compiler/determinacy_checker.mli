(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_parser
open Ast
open Compiler_data

type t [@@ deriving show, ord]

type func_map [@@ deriving show, ord]

val empty_fmap : func_map

val check_clause : loc:Loc.t -> functional_preds:func_map -> 
  ScopedTerm.t -> unit

val merge : func_map -> func_map -> func_map

class merger : func_map ->
  object
    method get_all_func : func_map
    method get_local_func : func_map
    method add_ty_abbr : F.t -> Scope.type_decl_id -> ScopedTypeExpression.t -> unit
    method add_func_ty_list : F.t -> TypeList.t -> TypeAssignment.overloaded_skema_with_id -> unit
  end
