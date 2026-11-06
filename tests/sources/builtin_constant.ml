(* Global symbols bound by MLConstants: the text of the builtins file declares
   them with no builtin keyword. Two more variants of (+), on strings and on
   lists, are symbols: the text tells them apart with = "test.1" and
   = "test.2" (the variants std.1 and std.2, on int and float, are in
   builtin.elpi). glob is a predicate whose rules are in Elpi. *)
open Elpi.API
open RawData

let plus_stringc = Constants.declare_global_symbol ~variant:"test.1" "+"
let plus_listc = Constants.declare_global_symbol ~variant:"test.2" "+"
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
symb (+) : string -> string -> string = "test.1".
symb (+) : list A -> list A -> list A = "test.2".
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

(* a symbol listed twice in MLConstants (as a symbol listed and implied) is
   bound once *)
let dup =
  let k = Constants.declare_global_symbol "dup.k" in
  BuiltIn.declare ~file_name:"dup.elpi" [
    BuiltIn.LPCode "data dk. symb dup.k : dk.";
    BuiltIn.MLConstants [k];
    BuiltIn.MLConstants [k];
  ]

(* the text of a builtins file declares each OCaml symbol once *)
let twice =
  let k = Constants.declare_global_symbol "twice" in
  BuiltIn.declare ~file_name:"twice.elpi" [
    BuiltIn.LPCode "data tw. symb twice : tw. symb twice : tw.";
    BuiltIn.MLConstants [k];
  ]

(* a symbol in a namespace is another name *)
let ns =
  let k = Constants.declare_global_symbol "nsk" in
  BuiltIn.declare ~file_name:"ns.elpi" [
    BuiltIn.LPCode "data nst. namespace inner { symb nsk : int -> nst. }";
    BuiltIn.LPCode "symb nsk : nst.";
    BuiltIn.MLConstants [k];
  ]

(* a symb with the name of an OCaml symbol that the file does not list (e.g.
   printed by a hand-written Conversion.t) *)
let unlisted =
  ignore (Constants.declare_global_symbol "unlisted");
  BuiltIn.declare ~file_name:"unlisted.elpi" [ BuiltIn.LPCode "data ul. symb unlisted : ul." ]

let program = {|
main :- sum ("a" + "b") S, sum ([1] + [2, 3]) L, X is 1 + 2,
  mk-glob 4 G, G, D = dup.k, N = nsk, I = inner.nsk 3, print S L X G D N I.
|}

let () =
  [ambiguous, "+ is the name of OCaml symbols with a variant: choose one with = \"test.1\" or = \"test.2\"";
   unbound, "glob, an OCaml symbol of unbound.elpi, is not declared by its text";
   twice, "twice, an OCaml symbol of twice.elpi, is declared twice by its text";
   unlisted, "unlisted is the name of an OCaml symbol (Constants.declare_global_symbol) that unlisted.elpi does not list"]
  |> List.iter (fun (b, expected) ->
    match Setup.init ~builtins:[Elpi.Builtin.std_builtins; b] () with
    | _ -> prerr_endline ("no error, expected: " ^ expected); exit 1
    | exception e ->
        let msg = Printexc.to_string e in
        prerr_endline msg;
        let rex = Str.regexp_string expected in
        if not (try ignore (Str.search_forward rex msg 0); true with Not_found -> false) then exit 1);
  let open Sepcomp.Sepcomp_template in
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins; builtins; dup; ns]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let base, _ = cc ~elpi ~flags ~base 1 program in
  exec (query ~elpi base)
