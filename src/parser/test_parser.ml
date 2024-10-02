open Elpi_parser
open Ast
open Ast.Program
open Ast.Term

let error s a1 a2 =
  Printf.eprintf "error parsing '%s':\n%!" s;
  let f1 = Filename.temp_file "parser_out" "txt" in
  let f2 = Filename.temp_file "parser_out" "txt" in
  let oc1 = open_out f1 in
  let oc2 = open_out f2 in
  output_string oc1 "\nnew:\n";
  output_string oc1 (Program.show a1);
  output_string oc2 "\nreference:\n";
  output_string oc2 (Program.show a2);
  flush_all ();
  close_out oc1;
  close_out oc2;
  let _ = Sys.command (Printf.sprintf "cat %s; cat %s;wdiff %s %s" f1 f2 f1 f2) in
  exit 1

let underscore loc = mkConst loc (Func.dummyname)

let mkClause loc attributes body =
  let open Clause in
  Clause { loc; attributes; body }

let mkLoc x y w z =
  { Loc.source_name = "(input)"; source_start = x; source_stop = y; line = w; line_starts_at = z}
  

let chunk s (p1,p2) =
  String.sub s p1.Lexing.pos_cnum (p2.Lexing.pos_cnum - p1.Lexing.pos_cnum)

let message_of_state s = try Error_messages.message s with Not_found -> "syntax error"

module Parser = Parse.Make(struct let resolver = Elpi_util.Util.std_resolver ~paths:[] () end)
let test s x y w z att b =
  let loc = Loc.initial "(input)" in
  let exp = [mkClause (mkLoc x y w z) att b] in
  let lexbuf = Lexing.from_string s in
  try
    let p = Parser.program_from ~loc lexbuf in
    if p <> exp then
      error s p exp
  with Parse.ParseError(loc,message) ->
    Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) message;
    exit 1

let testR s x y w z attributes to_match to_remove guard new_goal =
  let exp = [Program.(Chr { Chr.to_match; to_remove; guard; new_goal; loc=(mkLoc x y w z); attributes })] in
  let lexbuf = Lexing.from_string s in
  let loc = Loc.initial "(input)" in
  try
    let p = Parser.program_from ~loc lexbuf in
    if p <> exp then
      error s p exp
  with Parse.ParseError(loc,message) ->
    Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) message;
    exit 1
     
let testT s x y w z attributes () =
  let lexbuf = Lexing.from_string s in
  let loc = Loc.initial "(input)" in
  try
    let p = Parser.program_from ~loc lexbuf in
    match p with
    | [Program.Pred _] -> ()
    | [Program.Type _] -> ()
    | _ -> 
      Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) "not a type declaration";
      exit 1
  with Parse.ParseError(loc,message) ->
      Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) message;
      exit 1
      
let testF s i msg =
  let lexbuf = Lexing.from_string s in
  let loc = Loc.initial "(input)" in
  try
    let _ = Parser.program_from ~loc lexbuf in
    Printf.eprintf "error, '%s' should not parse\n%!" s;
    exit 1
  with Parse.ParseError(loc,message) ->
    if not @@ Str.string_match (Str.regexp_case_fold msg) message 0 then begin
      Printf.eprintf "error, '%s' fails with message '%s'\nwhich does not match '%s'\n%!" s message msg;   
      exit 1;
    end;
    if loc.Loc.source_start <> i then begin
      Printf.eprintf "error, '%s' fails at %d instead of %d\n%!" s loc.Loc.source_start i;
      exit 1;
    end


let (|-) a n ?(bug=false) b =
  let a1 = a.loc.source_start in
  let b2 = b.loc.source_stop in
  mkApp (mkLoc a1 b2 1 0) [mkCon (mkLoc (n + (if bug then -1 else 0)) (n+1) 1 0) ":-";a;b]


let lam x n b =
  let stop = b.loc.source_stop in
  mkLam (mkLoc n stop 1 0) x b
let mkNil = mkNil (mkLoc 1 0 1 0)
let mkSeq = mkSeq (mkLoc 1 0 1 0)
let c ?(bug=false) n s =
  mkCon (mkLoc (n + (if bug then -1 else 0)) n 1 0) s

let minl = List.fold_left (fun n x -> min n x.loc.source_start) max_int
let maxl = List.fold_left (fun n x -> max n x.loc.source_stop) min_int
let app a n ?(bug=false) b =
  let a1 = minl (c n a :: b) in
  let b2 = maxl (c n a :: b) in
  mkApp (mkLoc a1 b2 1 0) (mkCon (mkLoc (n + (if bug then -1 else 0)) (n + String.length a  - 1) 1 0) a :: b)
let str s = mkC (mkLoc 1 0 1 0) (cstring.Elpi_util.Util.CData.cin s)

let ss t = { Chr.eigen = underscore (mkLoc 1 0 1 0); context = underscore (mkLoc 1 0 1 0); conclusion = t }
let s e g t = { Chr.eigen = e; context = g; conclusion = t }

let bug n = n-1

let _ =
  (*    01234567890123456789012345 *)
  test  "p :- q."           1 6  1 0 [] ((c 1 "p" |- 3) (c 6 "q"));
  test  "p:- q."            1 5  1 0 [] ((c 1 "p" |- 2) ~bug:true (c 5 "q"));
  test  " p :- q."          2 7  1 0 [] ((c 2 "p" |- 4) (c 7 "q"));
  test  " p  :- q."         2 8  1 0 [] ((c 2 "p" |- 5) (c 8 "q"));
  (*    01234567890123456789012345 *)
  test  "p :- q r."         1 8  1 0 [] ((c 1 "p" |- 3) @@ app "q" 6 [c 8 "r"]);
  test  "p :- ! , q."       1 10 1 0 [] ((c 1 "p" |- 3) @@ app "," 8 [c 6 "!"; c 10 "q"]);
  test  "p :- !, q."        1 9  1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug:true 7 [c 6 "!"; c 9 "q"]);
  test  "p :- q r s."       1 10 1 0 [] ((c 1 "p" |- 3) @@ app "q" 6 [c 8 "r";c 10 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- x \\ q r."    1 12 1 0 [] ((c 1 "p" |- 3) @@ lam "x" 6 (app "q" 10 [c 12 "r"]));
  test  "p :- _ \\ q r."    1 12 1 0 [] ((c 1 "p" |- 3) @@ lam "%dummy" 6 (app "q" 10 [c 12 "r"]));
  test  "(A ; B) :- A."     1 12 1 0 [] ((app ";" 4 [c ~bug:true 2 "A";c 6 "B"] |- 9) @@ c 12 "A");
  (*    01234567890123456789012345 *)
  test  "p :- pi x \\ q."   1 13 1 0 [] ((c 1 "p" |- 3) @@ app "pi" 6 [lam "x" 9 (c 13 "q")]);
  test  "p :- q, r."        1 9  1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug:true 7 [c 6 "q";c 9 "r"]);
  test  "p :- f q, r."      1 11 1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug:true 9 [app "f" 6 [c 8 "q"];c 11 "r"]);
  test  "p :- q, r, s."     1 12 1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug:true 7 [c 6 "q"; c 9 "r"; c 12 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- q + r * s."   1 14 1 0 [] ((c 1 "p" |- 3) @@ app "+" 8 [c 6 "q"; app "*" 12 [c 10 "r";c 14 "s"]]);
  (* 
  test  "p :- q + r , s."   0 14 1 0 [] (c"p" |- "," @ ["+" @ [c"q"; c"r" ]; c"s"]);
  test  "p :- q && r = s."  0 15 1 0 [] (c"p" |- "=" @ ["&&" @ [c"q"; c"r"]; c"s"]);
  test  "q && r x || s."    0 13 1 0 [] ("||" @ ["&&" @ [c"q";"r"@[c"x"]]; c"s"]);
  test  "f x ==> y."        0 9 1 0 []  ("==>" @ ["f" @ [c"x"]; c"y"]);
  test  "p :- !, (s X) = X, q." 0 20 1 0 [] (c"p" |- "," @ [c"!";"=" @ ["s" @ [c"X"]; c"X"]; c"q"]);
  test  "p :- []."          0 7  1 0 [] (c"p" |- mkNil);
  test  "name."             0 4  1 0 [] (c "name");
  test  "p :- a => b => c." 0 16 1 0 [] (":-" @ [c"p";"=>" @ [c"a";"=>"@[c"b";c"c"]]]); 
  (*    01234567890123456789012345 *)
  test  "p :- [a,b]."       0 10  1 0 [] (c"p" |- mkSeq [c"a";c"b";mkNil]);
  test  "p :- [a,{b}]."     0 12  1 0 [] (c"p" |- mkSeq [c"a";"%spill"@[c"b"];mkNil]);
  test  "p :- [(a + b)]."   0 14  1 0 [] (c"p" |- mkSeq ["+" @ [c"a";c"b"];mkNil]);
  test  "p :- [a + b]."     0 12  1 0 [] (c"p" |- mkSeq ["+" @ [c"a";c"b"];mkNil]);
  test  "p :- [f a,b]."     0 12  1 0 [] (c"p" |- mkSeq ["f" @ [c"a"];c"b";mkNil]);
  test  "p :- [(a,b)]."     0 12  1 0 [] (c"p" |- mkSeq ["," @ [c"a";c"b"];mkNil]);
  test  "p :- [a,b|c]."     0 12  1 0 [] (c"p" |- mkSeq [c"a";c"b";c"c"]);
  test  "p :- [a,b\\@f, x\\b]." 0 18  1 0 [] (c"p" |- mkSeq [c"a";"b" --> ("," @ [c"@f"; "x" --> c"b"]);mkNil]);
  test  "X is a."           0 6  1 0 [] ("is" @ [c"X";c"a"]);
  testF "p :- f use_sig."   14 ".*term expected";
  testF "X is ."            6 ".*expects a right hand side";
  testF "X + ."             5 ".*expects a right hand side";
  testF "X * ."             5 ".*expects a right hand side";
  test  "p :- X is a, Y is b."   0 19 1 0 [] (":-" @ [c"p";"," @ ["is" @ [c"X";c"a"];"is" @ [c"Y";c"b"]]]);
  test  "p (f x\\ _ as y)." 0 15 1 0 [] ("p" @ ["as" @ ["f"@["x" --> c"%dummy"];c"y"]]);
  (*    01234567890123456789012345 *)
  testF ":-"                2 "unexpected start";
  testF "type ( -> :-"      12 ".*parenthesis.*expected";
  testF "+"                 1 "unexpected start";
  testF "x. x)"             5 "unexpected keyword";
  testF "x. x]"             5 "unexpected keyword";
  testF "x. +"              4 "unexpected start";
  test  ":name \"x\" x."     0 11 1 0 [Name "x"] (c"x");
  testT ":index (1) \"foobar\" pred x."     0 11 1 0 [Index ([1],Some "foobar")] ();
  testT ":index (1) pred x."     0 11 1 0 [Index ([1], None)] ();
  testF "p :- g (f x) \\ y." 14 ".*bind.*must follow.*name.*";
  testF "foo i:term, o:term. foo A B :- A = [B]." 6 "unexpected keyword";
  (*    01234567890123456789012345 *)
  testF ":nam \"x\" x."     4 "attribute expected";
  testR "rule p (q r)."     0 12 1 0 [] [ss (c"p");ss ("q" @ [c"r"])] [] None None;
  testR "rule (E : G ?- r)."0 17 1 0 [] [s (c "E") (c"G") (c"r")] [] None None;
  test  "p :- f \".*\\\\.aux\"." 0 17 1 0 [] (":-" @ [c"p";"f"@ [str ".*\\.aux"]]);
  *)
;; 

(* test that all families of tokens are parsed as such *)
let sanity_check : unit =
  let open Elpi_lexer_config in
  let open Lexer_config in
  let open Tokens in
  let open Elpi_util in
  let extensible_SYMB =
    mixfix_symbols |> List.map (fun { tokens; fixity; _ } ->
      Util.map_filter (fun x ->
        let start, mk_token, enclose, x =
          match x with
          | Fixed { the_token; mk_token; _ } ->
              the_token, (fun _ -> mk_token), None, None
          | Extensible ({ start; mk_token; non_enclosed ; at_least_one_char; _ } as e)->
              let start = if at_least_one_char then start ^ "x" else start in
              start, mk_token, (if non_enclosed then Some (fun x -> start ^ x ^ start) else None), Some e in
    let tok = Lexer.token (Lexing.from_string start) in
    let token = mk_token start in
    assert(tok = token);
    begin try match fixity with
    | Infix | Infixl | Infixr ->
        ignore(Parser.Internal.infix_SYMB Lexer.token (Lexing.from_string start))
    | Postfix ->
        ignore(Parser.Internal.postfix_SYMB Lexer.token (Lexing.from_string start))
    | Prefix ->
        ignore(Parser.Internal.prefix_SYMB Lexer.token (Lexing.from_string start))
    with _ -> Printf.eprintf "error parsing %s\n" start; exit 1
    end;
    begin match enclose with
    | None -> ()
    | Some f ->
      let v = f "xx" in
      assert(CONSTANT v = Lexer.token (Lexing.from_string v));
    end;
    x) tokens) |> List.concat |> List.length in
  assert(extensible_SYMB = 14)

