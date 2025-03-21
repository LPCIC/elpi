(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Elpi_util.Util

type t = (TypeAssignment.skema_w_id * Loc.t) F.Map.t [@@deriving show, ord]

val check_clause : uf:IdPos.UF.t -> loc:Loc.t -> env:t -> ScopedTerm.t -> unit
