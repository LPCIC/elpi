(* Global symbols bound by MLConstants: the text of the builtins file declares
   them with no builtin keyword. Two more variants of (+), on strings and on
   lists, are symbols: the text tells them apart with = "N" (the variants 1
   and 2, on int and float, are in builtin.elpi). glob is a predicate whose
   rules are in Elpi. *)
open Elpi.API
open RawData

let plus_stringc = Constants.declare_global_symbol ~variant:3 "+"
let plus_listc = Constants.declare_global_symbol ~variant:4 "+"
let globc = Constants.declare_global_symbol "glob"

let builtins =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
  let string_of ~depth t =
    match look ~depth t with
    | CData s when RawOpaqueData.is_string s -> RawOpaqueData.to_string s
    | _ -> raise No_clause in
  declare ~file_name:"plus.elpi" [
    LPCode {|
symb (+) : string -> string -> string = "3".
symb (+) : list A -> list A -> list A = "4".
func glob int.
glob 4.
|};
    MLConstants [plus_stringc; plus_listc; globc];
    MLCode(Pred("sum",
      In(BuiltInData.any, "E",
      Out(BuiltInData.any, "V",
      Full(unit_ctx, "V is the value of E, a sum of two strings or of two lists"))),
      (fun e _ ~depth _ _ state ->
        match look ~depth e with
        | App (c, a, [b]) when c == plus_stringc ->
            state, !: (RawOpaqueData.of_string (string_of ~depth a ^ string_of ~depth b)), []
        | App (c, a, [b]) when c == plus_listc ->
            state, !: (Utils.list_to_lp_list (Utils.lp_list_to_list ~depth a @ Utils.lp_list_to_list ~depth b)), []
        | _ -> raise No_clause)),
    DocAbove);
    MLCode(Pred("mk-glob",
      In(BuiltInData.int, "N",
      Out(BuiltInData.any, "G",
      Full(unit_ctx, "G is glob N"))),
      (fun n _ ~depth:_ _ _ state -> state, !: (mkApp globc (RawOpaqueData.of_int n) []), [])),
    DocAbove);
  ]

(* a symb with the name of two MLConstants must say which one *)
let ambiguous =
  BuiltIn.declare ~file_name:"ambiguous.elpi" [
    BuiltIn.LPCode "symb (+) : string -> string -> string.";
    BuiltIn.MLConstants [plus_stringc; plus_listc];
  ]

(* each MLConstants needs a declaration *)
let unbound =
  BuiltIn.declare ~file_name:"unbound.elpi" [ BuiltIn.MLConstants [globc] ]

let program = {|
main :- sum ("a" + "b") S, sum ([1] + [2, 3]) L, X is 1 + 2,
  mk-glob 4 G, G, print S L X G.
|}

let () =
  [ambiguous, "+ is the name of several OCaml symbols (variants 3, 4): choose one with = \"N\"";
   unbound, "glob (variant 0), an OCaml symbol of unbound.elpi, is not declared by its text"]
  |> List.iter (fun (b, expected) ->
    match Setup.init ~builtins:[Elpi.Builtin.std_builtins; b] () with
    | _ -> prerr_endline ("no error, expected: " ^ expected); exit 1
    | exception e ->
        let msg = Printexc.to_string e in
        prerr_endline msg;
        let rex = Str.regexp_string expected in
        if not (try ignore (Str.search_forward rex msg 0); true with Not_found -> false) then exit 1);
  let open Sepcomp.Sepcomp_template in
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins; builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let base, _ = cc ~elpi ~flags ~base 1 program in
  exec (query ~elpi base)
