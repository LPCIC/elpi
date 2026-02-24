open Elpi.API

let cc ~elpi ~flags ~base ?builtins i u =
    Compile.unit ~elpi ~flags ~base ?builtins
     (Compile.scope ~elpi ~flags ?builtins
      (Parse.program_from ~elpi ~loc:(Ast.Loc.initial (Printf.sprintf "<u%d>" i))
        (Lexing.from_string u)))

let u1 = {| pred p. p. |}

let c = AlgebraicData.(declare {
  ty = Conversion.TyName "stuff";
  doc = "doc";
  pp = (fun fmt (x : int) -> ());
  constructors = [
    K("stuff","",A(BuiltInData.int,N),B (fun x -> x),M (fun ~ok ~ko:_ x -> ok x));
  ];
}
) |> ContextualConversion.(!<)

let b2 =
  let open BuiltIn in
  let open BuiltInPredicate in
  let cx = MLData c in
  let q = MLCode(Pred("q",In(c,"xxx",Easy "bla"),(fun i ~depth -> Printf.eprintf "ok %d\n%!" i)),DocAbove) in
  declare ~file_name:"doc" [ cx; q ]

let main =
  let elpi =
    Setup.init ~builtins:[Elpi.Builtin.std_builtins] ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in

  let u1 = cc ~elpi ~flags ~base 1 u1 in

  let u2 = cc ~elpi ~flags ~base ~builtins:b2 2 "" in

  let base = Compile.extend ~base u1 in

  let ex1 =
    Compile.optimize  @@
      Compile.query base
        (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "p")) in

  begin match Execute.once ex1 with
  | Execute.Success _ -> ()
  | _ -> exit 1
  end;

  let base = Compile.extend ~base u2 in
  let ex2 =
    Compile.optimize  @@
      Compile.query base
        (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "p, q (stuff 46)")) in

  begin match Execute.once ex2 with
  | Execute.Success _ -> ()
  | _ -> exit 1
  end;
