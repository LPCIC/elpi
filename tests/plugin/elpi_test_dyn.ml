(* a plugin dynlinked by the elpi command: package elpi-test-dyn *)
open Elpi.API

let () =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  ignore @@ Plugin.register ~name:"elpi-test-dyn" [
    MLCode(Pred("dyn.double", In(BuiltInData.int, "N", Out(BuiltInData.int, "M", Easy "M is 2 * N")),
      (fun n _ ~depth:_ -> !: (2 * n))), DocAbove);
  ]
