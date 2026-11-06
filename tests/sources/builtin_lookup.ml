(* OCaml code and an Elpi predicate: hyp is an ordinary predicate (no
   builtin, no global symbol), OCaml finds its constant in the running program
   with Constants.lookup *)
open Elpi.API
open RawData

let hypc = Constants.lookup "hyp"

let builtins =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
  declare ~file_name:"lookup.elpi" [
    MLCode(Pred("mk-hyp",
      In(BuiltInData.int, "N",
      Out(BuiltInData.any, "G",
      Full(unit_ctx, "G is hyp N"))),
      (fun n _ ~depth:_ _ _ state -> state, !: (mkApp (hypc state) (RawOpaqueData.of_int n) []), [])),
    DocAbove);
    MLCode(Pred("is-hyp",
      In(BuiltInData.any, "G",
      Full(unit_ctx, "G is hyp _")),
      (fun g ~depth _ _ state ->
        match look ~depth g with
        | App (c, _, []) when c == hypc state -> state, (), []
        | _ -> raise No_clause)),
    DocAbove);
  ]

let program = {|
func hyp int.
hyp 3.

main :- mk-hyp 3 G, is-hyp G, G, not (is-hyp 3), print G.
|}

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins; builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let base, _ = cc ~elpi ~flags ~base 1 program in
  exec (query ~elpi base)
