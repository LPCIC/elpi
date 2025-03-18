(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Elpi_util.Util

type t [@@deriving show, ord]

val empty_env : t
val merge : t -> t -> t

val check_clause : uf:IdPos.UF.t -> loc:Loc.t -> env:t -> ScopedTerm.t -> unit

class merger : t -> object
  method get_all_func : t
  method get_local_func : t
  method add_ty_abbr : ScopedTypeExpression.t -> unit
  method merge : t
end
