(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Elpi_util.Util
module Union_find : Union_find.S with type key = IdPos.t and type t = IdPos.t IdPos.Map.t

type t [@@deriving show, ord]

val empty_fmap : t
val check_clause : ?uf:Union_find.t -> loc:Loc.t -> env:t -> modes:(mode * Loc.t) F.Map.t -> ScopedTerm.t -> unit
val merge : t -> t -> t
val remove : t -> IdPos.t -> t

class merger : t -> object
  method get_all_func : t
  method get_local_func : t
  method add_ty_abbr : Scope.type_decl_id -> ScopedTypeExpression.t -> unit
  method add_func_ty_list : TypeList.t -> IdPos.t list -> unit
  method merge : t
end
