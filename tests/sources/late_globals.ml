(* OCaml code linked after Setup.init (as a dynlinked plugin would be): it
   declares a global symbol, a data type (AlgebraicData) and a builtins file
   using them, which an existing base accumulates *)
open Elpi.API
open RawData
open Sepcomp.Sepcomp_template

type shape = Circle of int | Square

(* everything below runs after Setup.init *)
let late () =
  let boxc = Constants.declare_global_symbol "box" in
  let shape = AlgebraicData.(declare {
    ty = Conversion.TyName "shape";
    doc = "a shape";
    pp = (fun fmt -> function Circle r -> Format.fprintf fmt "circle %d" r | Square -> Format.fprintf fmt "square");
    constructors = [
      K("circle","a circle",A(BuiltInData.int,N),
        B (fun r -> Circle r),
        M (fun ~ok ~ko -> function Circle r -> ok r | _ -> ko ()));
      K("square","a square",N,
        B Square,
        M (fun ~ok ~ko -> function Square -> ok | _ -> ko ()));
    ];
  }) |> ContextualConversion.(!<) in
  (* a parametric data type: each instance has the same constructor *)
  let tagged a = AlgebraicData.(declare {
    ty = Conversion.TyApp ("tagged", a.Conversion.ty, []);
    doc = "a tagged value";
    pp = (fun fmt (s, _) -> Format.fprintf fmt "tag %s" s);
    constructors = [
      K("tag","",A(BuiltInData.string,A(a,N)),
        B (fun s x -> (s, x)),
        M (fun ~ok ~ko:_ (s, x) -> ok s x));
    ];
  }) |> ContextualConversion.(!<) in
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
  declare ~file_name:"late.elpi" [
    MLData shape;
    MLData (tagged (BuiltInData.poly "A"));
    LPCode "data box. symb box : int -> box.";
    MLConstants [boxc];
    MLCode(Pred("mk-box",
      In(BuiltInData.int, "N",
      Out(BuiltInData.any, "B",
      Full(unit_ctx, "B is box N"))),
      (fun n _ ~depth:_ _ _ state -> state, !: (mkApp boxc (RawOpaqueData.of_int n) []), [])),
    DocAbove);
    MLCode(Pred("box-size",
      In(BuiltInData.any, "B",
      Out(BuiltInData.int, "N",
      Full(unit_ctx, "B is box N"))),
      (fun b _ ~depth _ _ state ->
        match look ~depth b with
        | App (c, n, []) when c == boxc ->
            (match look ~depth n with
             | CData d when RawOpaqueData.is_int d -> state, !: (RawOpaqueData.to_int d), []
             | _ -> raise No_clause)
        | _ -> raise No_clause)),
    DocAbove);
    MLCode(Pred("area",
      In(shape, "S",
      Out(BuiltInData.int, "A",
      Easy "A is the area of S, rounded")),
      (fun s _ ~depth:_ -> !: (match s with Circle r -> 3 * r * r | Square -> 1))),
    DocAbove);
    MLCode(Pred("grow",
      In(shape, "S",
      Out(shape, "T",
      Easy "T is S, twice as large")),
      (fun s _ ~depth:_ -> !: (match s with Circle r -> Circle (2 * r) | Square -> Square))),
    DocAbove);
    MLCode(Pred("tag-int",
      In(BuiltInData.int, "N",
      Out(tagged BuiltInData.int, "T",
      Easy "T is N tagged int")),
      (fun n _ ~depth:_ -> !: ("int", n))),
    DocAbove);
  ]

let () =
  let elpi = init () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let base, _ = cc ~elpi ~flags ~base 1 {| func p -> int. p 1. func before. before :- p X, print "before" X. |} in
  if not (try_exec (ok_query @@ Compile.query base (ok_goal ~elpi "before"))) then exit 1;
  (* the plugin is loaded now *)
  let builtins = late () in
  let u = ok @@ Compile.unit ~elpi ~flags ~base (Compile.scope_builtins ~elpi ~flags builtins) in
  let base = extend ~flags ~base u in
  let base, _ = cc ~elpi ~flags ~base 2 {|
main :-
  mk-box 3 B, B = box N, box-size (box 4) M,
  area (circle 2) A, area square A1,
  grow (circle 2) C, C = circle R,
  tag-int 7 (tag G V),
  print N M A A1 C R G V.
|} in
  exec (query ~elpi base)
