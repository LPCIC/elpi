let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_tctx _ _ = ()
type tctx = TEntry of (string[@elpi.key]) * bool
[@@elpi.index (module String)]
[@@deriving elpi { declaration }]

let pp_ty _ _ = ()
type ty =
  | TVar of string [@elpi.var tctx]
  | TApp of string * ty
  | TAll of bool * string * (ty[@elpi.binder tctx (fun b s -> TEntry(s,b))])
[@@deriving elpi { declaration; }]


let pp_ctx _ _ = ()
type ctx = Entry of (string[@elpi.key]) * ty
[@@elpi.index (module String)]
[@@deriving elpi { declaration } ]

let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var ctx]
  | App of term * term
  | Lam of ty * string * (term[@elpi.binder ctx (fun b s -> Entry(s,b))])
[@@deriving elpi { declaration; context = [ctx;tctx] }]

open Elpi.API

let in_ctx : (tctx ContextualConversion.ctx_entry RawData.Constants.Map.t * ctx ContextualConversion.ctx_entry RawData.Constants.Map.t, Data.constraints) ContextualConversion.ctx_readback = in_ctx

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()