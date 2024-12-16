(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Elpi_util.Util

type t [@@ deriving show, ord]

val empty_fmap : t

val check_clause : loc:Loc.t -> env:t -> modes:(mode*Loc.t) F.Map.t -> ScopedTerm.t -> unit

val merge : t -> t -> t

class merger : t ->
  object
    method get_all_func : t
    method get_local_func : t
    method add_ty_abbr : Scope.type_decl_id -> ScopedTypeExpression.t -> unit
    method add_func_ty_list : TypeList.t -> TypeAssignment.overloaded_skema_with_id -> unit
    method merge : t
  end
