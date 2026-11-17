(* the plugin of findlib package elpi-test-missing, whose installed stub is
   stale: elpi -check-package reports it *)
open Elpi.API

let () =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  ignore @@ Plugin.register ~name:"elpi-test-missing" [
    MLCode(Pred("missing.triple", In(BuiltInData.int, "N", Out(BuiltInData.int, "M", Easy "M is 3 * N")),
      (fun n _ ~depth:_ -> !: (3 * n))), DocAbove);
  ]
