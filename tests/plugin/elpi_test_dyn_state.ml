(* a plugin that declares a state component: the plugin of findlib
   package elpi-test-dyn.state,
   to be loaded before Setup.init *)
open Elpi.API

let counter = State.declare_component ~name:"test-dyn:counter"
  ~pp:(fun fmt n -> Format.fprintf fmt "%d" n) ~init:(fun () -> 0) ~start:(fun x -> x) ()

let () =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
  ignore @@ Plugin.register ~name:"elpi-test-dyn.state" [
    MLCode(Pred("dyn.tick", Out(BuiltInData.int, "N", Full(unit_ctx, "N is the number of ticks so far")),
      (fun _ ~depth:_ _ _ state ->
        let state, n = State.update_return counter state (fun n -> n + 1, n + 1) in
        state, !: n, [])), DocAbove);
  ]
