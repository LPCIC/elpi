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
let mkNil ?(bug=false) n = mkNil (mkLoc (n + (if bug then -1 else 0)) n 1 0)
let mkSeq n m = mkSeq (mkLoc n m 1 0)
let c ?(bug=false) n ?len s =
  let len = match len with None -> String.length s | Some x -> x in
  mkCon (mkLoc (n + (if bug then -1 else 0)) (n + len - 1) 1 0) s

let underscore ?bug ?(len=1)n = c ?bug ~len n Func.(show dummyname)

let minl = List.fold_left (fun n x -> min n x.loc.source_start) max_int
let maxl = List.fold_left (fun n x -> max n x.loc.source_stop) min_int
let app a ?(len=String.length a) n ?(parenl=false) ?(parenr=false) ?(bug=false) b =
  let c = c ~bug n ~len a in
  let a1 = minl (c :: b) + (if parenl then -1 else 0) in
  let b2 = maxl (c :: b) + (if parenr then 1 else 0) in
  mkApp (mkLoc a1 b2 1 0) (c :: b)

let paren t = { t with loc = Loc.extend 1 t.loc }

let spill n m ?bug b =
  let len = 1 in
  let a = "%spill" in
  let c = c ?bug n ~len a in
  mkApp (mkLoc (n + (if bug = Some true then -1 else 0)) m 1 0) [c ; b]

let str n m s = mkC (mkLoc n m 1 0) (cstring.Elpi_util.Util.CData.cin s)

let ss n m t = { Chr.eigen = underscore n ~len:m; context = underscore n ~len:m; conclusion = t }
let s e g t = { Chr.eigen = e; context = g; conclusion = t }

(* ~bug:true means that the token starts one char to the left of what is declared
   I could not understand where the bug is, but since it mainly affects infix symbols
   it should not make error reporting too imprecise in practice
*)
let bug = true

let _ =
  (*    01234567890123456789012345 *)
  test  "p :- q."           1 6  1 0 [] ((c 1 "p" |- 3) (c 6 "q"));
  test  "p:- q."            1 5  1 0 [] ((c 1 "p" |- 2) ~bug (c 5 "q"));
  test  " p :- q."          2 7  1 0 [] ((c 2 "p" |- 4) (c 7 "q"));
  test  " p  :- q."         2 8  1 0 [] ((c 2 "p" |- 5) (c 8 "q"));
  (*    01234567890123456789012345 *)
  test  "p :- q r."         1 8  1 0 [] ((c 1 "p" |- 3) @@ app "q" 6 [c 8 "r"]);
  test  "p :- ! , q."       1 10 1 0 [] ((c 1 "p" |- 3) @@ app "," 8 [c 6 "!"; c 10 "q"]);
  test  "p :- !, q."        1 9  1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug 7 [c 6 "!"; c 9 "q"]);
  test  "p :- q r s."       1 10 1 0 [] ((c 1 "p" |- 3) @@ app "q" 6 [c 8 "r";c 10 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- x \\ q r."    1 12 1 0 [] ((c 1 "p" |- 3) @@ lam "x" 6 (app "q" 10 [c 12 "r"]));
  test  "p :- _ \\ q r."    1 12 1 0 [] ((c 1 "p" |- 3) @@ lam "%dummy" 6 (app "q" 10 [c 12 "r"]));
  test  "(A ; B) :- A."     1 12 1 0 [] ((app ";" 4 [c ~bug 2 "A";c 6 "B"] |- 9) @@ c 12 "A");
  (*    01234567890123456789012345 *)
  test  "p :- pi x \\ q."   1 13 1 0 [] ((c 1 "p" |- 3) @@ app "pi" 6 [lam "x" 9 (c 13 "q")]);
  test  "p :- q, r."        1 9  1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug 7 [c 6 "q";c 9 "r"]);
  test  "p :- f q, r."      1 11 1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug 9 [app "f" 6 [c 8 "q"];c 11 "r"]);
  test  "p :- q, r, s."     1 12 1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug 7 [c 6 "q"; c 9 "r"; c 12 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- q + r * s."   1 14 1 0 [] ((c 1 "p" |- 3) @@ app "+" 8 [c 6 "q"; app "*" 12 [c 10 "r";c 14 "s"]]);
  test  "p :- q + r , s."   1 14 1 0 [] ((c 1 "p" |- 3) @@ app "," 12 [app "+" 8 [c 6 "q";c 10 "r"]; c 14 "s"]);
  test  "p :- q && r = s."  1 15 1 0 [] ((c 1 "p" |- 3) @@ app "=" 13 [app "&&" 8 [c 6 "q"; c 11 "r"]; c 15 "s"]);
  test  "q && r x || s."    1 13 1 0 [] (app "||" 10 [app "&&" 3 [c 1 "q"; app "r" 6 [c 8 "x"]]; c 13 "s"]);
  (*    01234567890123456789012345 *)
  test  "f x ==> y."        1 9 1 0 []  (app "==>" 5 [app "f" 1 [c 3 "x"]; c 9 "y"]);
  test  "p :- !, (s X) = X, q." 1 20 1 0 [] ((c 1 "p" |- 3) @@ app "," ~bug 7 [c 6 "!";app "=" 15 [app "s" ~bug 10 [c 12 "X"]; c 17 "X"]; c 20 "q"]);
  test  "p :- [ ]."         1 8  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 8 [mkNil 8]);
  test  "p :- []."          1 7  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 7 [mkNil ~bug 7]);
  test  "name."             1 4  1 0 [] (c 1 "name");
  test  "p :- a => b => c." 1 16 1 0 [] (app ":-" 3 [c 1 "p";app "=>" 8 [c 6 "a";app "=>" 13 [c 11 "b";c 16 "c"]]]); 
  (*    01234567890123456789012345 *)
  test  "p :- [ a , b ]."   1 14  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 14 [c 8 "a";c 12 "b";mkNil 14]);
  test  "p :- [a,b]."       1 10  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 10 [c 7 ~bug "a";c 9 ~bug "b";mkNil ~bug 10]);
  test  "p :- [ a , {b} ]." 1 16  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 16 [c 8"a";spill 12 14 (c 13 ~bug "b");mkNil 16]);
  test  "p :- [a,{b}]."     1 12  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 12 [c 7 ~bug "a";spill 9 11 ~bug (c ~bug 10 "b");mkNil ~bug 12]);
  (*    01234567890123456789012345 *)
  test  "p :- [(a + b)]."   1 14  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 14 [app "+" 10 [c ~bug 8 "a";c 12 "b"];mkNil ~bug 14]);
  test  "p :- [a + b]."     1 12  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 12 [app "+" 9 [c 7 ~bug "a";c 11 "b"];mkNil ~bug 12]);
  test  "p :- [ f a , b ]." 1 16  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 16 [app "f" 8 [c 10 "a"];c 14 "b";mkNil 16]);
  test  "p :- [f a,b]."     1 12  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 12 [app "f" 7 ~bug [c 9 "a"];c ~bug 11 "b";mkNil ~bug 12]);
  (*    01234567890123456789012345 *)
  test  "p :- [(a,b)]."     1 12  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 12 [app "," 9 ~bug [c ~bug 8 "a";c ~bug 10 "b"];mkNil ~bug 12]);
  test  "p :- [a,b|c]."     1 12  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 12 [c ~bug 7 "a";c 9 ~bug "b";c 11 ~bug "c"]);
  test  "p :- [ a , b \\ @f , x \\ b ]." 1 27  1 0 [] ((c 1 "p" |- 3) @@ mkSeq 6 27 [c 8 "a"; lam "b" 12 (app "," 19 [ c 16 "@f"; lam "x" 21  (c 25 "b")]);mkNil 27]);
  (*    0123456789012345678901234567890 *)
  test  "X is a."           1 6  1 0 [] (app "is" 3 [c 1 "X";c 6 "a"]);
  testF "p :- f use_sig."   14 ".*term expected";
  testF "X is ."            6 ".*expects a right hand side";
  testF "X + ."             5 ".*expects a right hand side";
  testF "X * ."             5 ".*expects a right hand side";
  test  "p :- X is a, Y is b." 1 19 1 0 [] (app ":-" 3 [c 1 "p"; app "," ~bug 12 [app "is" 8 [c 6 "X";c 11 "a"];app "is" 16 [c 14 "Y";c 19 "b"]]]);
  (*    0123456789012345678901234567890 *)
  test  "p (f x\\ _ as y)." 1 15 1 0 [] (app "p" 1 [app ~parenr:true "as" 11 [app "f" ~bug 4 [lam "x" 6  (underscore 9)]; c 14 "y"]]); (* parenl implied by bug *)
  (*    01234567890123456789012345 *)
  testF ":-"                2 "unexpected start";
  testF "type ( -> :-"      12 ".*parenthesis.*expected";
  testF "+"                 1 "unexpected start";
  testF "x. x)"             5 "unexpected keyword";
  testF "x. x]"             5 "unexpected keyword";
  testF "x. +"              4 "unexpected start";
  (*    01234567890123456789012345 *)
  test  ":name \"x\" x."    1 11 1 0 [Name "x"] (c 11 "x");
  testT ":index (1) \"foobar\" pred x." 1 11 1 0 [Index ([1],Some "foobar")] ();
  testT ":index (1) pred x."     1 11 1 0 [Index ([1], None)] ();
  testF "p :- g (f x) \\ y." 14 ".*bind.*must follow.*name.*";
  testF "foo i:term, o:term. foo A B :- A = [B]." 6 "unexpected keyword";
  (*    01234567890123456789012345 *)
  testF ":nam \"x\" x."     4 "attribute expected";
  testR "rule p (q r)."     1 12 1 0 [] [ss 6 1 (c 6 "p");ss 8 5 (app "q" ~bug 9 [c 11 "r"])] [] None None;
  testR "rule (E : G ?- r)." 1 17 1 0 [] [s (c ~bug 7 "E") (c 11 "G") (c 16 "r")] [] None None;
  test  "p :- f \".*\\\\.aux\"." 1 17 1 0 [] (app ":-" 3 [c 1 "p";app "f" 6  [str 8 17 ".*\\.aux"]]);
  (*    01234567890123456789012345 *)

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

