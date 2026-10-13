let file_name = Sys.argv.(1)

open Elpi.API

(* https://github.com/LPCIC/elpi/issues/467: a variable embedded under a
   binder must be the bound variable of the lambda, i.e. the term is
   lam c0\ c0, not lam c0\ c1 *)

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

type tctx = Entry of (string[@elpi.key "term"])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type term =
  | Var of string [@elpi.var tctx]
  | Lam of string * (term[@elpi.binder "term" tctx (fun s -> Entry s)])
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () =
  Ppx_tests_lib.protect (fun () ->
    Ppx_tests_lib.document builtin;
    let fmt, close = Ppx_tests_lib.formatter_on_output () in
    let elpi = Ppx_tests_lib.init builtin in
    Format.fprintf fmt "@\n/* OUTPUT@\n";
    let finish () = Format.fprintf fmt "*/@\n"; close () in
    try
      ignore (RawQuery.compile_raw_term (Compile.empty_base ~elpi) (fun s ->
        let ctx = new ctx_for_term [] s in
        let (_, t, _) as r =
          elpi_embed_term ~depth:0 ctx RawData.no_constraints s
            (Lam ("x", Var "x")) in
        Format.fprintf fmt "%a@\n" (RawPp.term 0) t;
        r));
      finish ()
    with e -> finish (); raise e)
