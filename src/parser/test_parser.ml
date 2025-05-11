open Elpi_parser
open Ast
open Ast.Program
open Ast.Term

let error s a1 a2 =
  Printf.eprintf "\n            (*          1         2         3 *)";
  Printf.eprintf "\n            (* 123456789012345678901234567890 *)";
  Printf.eprintf "\nerror parsing '%s':\n%!" s;
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
  Clause { loc; attributes; body; needs_spilling = () }

let mkLoc x y w z =
  { Loc.client_payload = None; source_name = "(input)"; source_start = x; source_stop = y; line = w; line_starts_at = z}
  

let chunk s (p1,p2) =
  String.sub s p1.Lexing.pos_cnum (p2.Lexing.pos_cnum - p1.Lexing.pos_cnum)

let message_of_state s = try Error_messages.message s with Not_found -> "syntax error"

module Parser = Parse.Make(struct let versions = Elpi_util.Util.StrMap.empty let resolver = Elpi_util.Util.std_resolver ~paths:[] () end)

let warn = ref None
let () = Elpi_util.Util.set_warn (fun ?loc ~id str -> warn := Some str)
let test s x y w z att ?warns b =
  let loc = Loc.initial "(input)" in
  let exp = [mkClause (mkLoc (x-1) y w z) att b] in
  let lexbuf = Lexing.from_string s in
  warn := None;
  try
    let p = Parser.program_from ~loc lexbuf in
    if p <> exp then error s p exp;
    match !warn, warns with
    | None, None -> ()
    | Some w, None -> Printf.eprintf "parsing '%s': unexpected warning:\n%s\n" s w; exit 1
    | None, Some _ -> Printf.eprintf "parsing '%s': expected warning not emitted\n" s; exit 1
    | Some w, Some rex ->
        if Str.(string_match (regexp rex) w 0) then () else (Printf.eprintf "parsing '%s': warning does not match:\n%s\n" s w; exit 1)
  with Parse.ParseError(loc,message) ->
    Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) message;
    exit 1

let testR s x y w z attributes to_match to_remove guard new_goal =
  let exp = [Program.(Chr { Chr.to_match; to_remove; guard; new_goal; loc=(mkLoc (x-1) y w z); attributes })] in
  let lexbuf = Lexing.from_string s in
  let loc = Loc.initial "(input)" in
  try
    let p = Parser.program_from ~loc lexbuf in
    if p <> exp then
      error s p exp
  with Parse.ParseError(loc,message) ->
    Printf.eprintf "error parsing '%s' at %s\n%s%!" s (Loc.show loc) message;
    exit 1
     
let testT s () =
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

let (|-) a n ?(parenl=false) b =
  let a1 = a.loc.source_start + (if parenl then -1 else 0) in
  let b2 = b.loc.source_stop in
  (* Printf.eprintf "%s a1=%d\n" ":-" a1; *)
  mkApp (mkLoc a1 b2 1 0) [mkCon (mkLoc (n - 1) (n+1) 1 0) ":-";a;b]


let lam x n ?ty ?(parensl=false) ?(parensr=false) b =
  let stop = b.loc.source_stop + (if parensr then 1 else 0) in
  let start = (n - 1 + (if parensl then -1 else 0)) in
  let xloc = mkLoc start (start + if x = "%dummy" then 1 else String.length x) 1 0 in
  mkLam (mkLoc (n - 1 + (if parensl then -1 else 0)) stop 1 0) x xloc ty b
let mkNil ?(len=2) n = mkNil (mkLoc (n) (n + len) 1 0)
let mkSeq n m = mkSeq ~loc:(mkLoc n m 1 0)
let c ?(bug=false) n ?len s =
  let len = match len with None -> String.length s | Some x -> x in
  mkCon (mkLoc (n ) (n + len) 1 0) s
let q n m n1 m1 ?kind data =
  let loc = mkLoc n m 1 0 in
  let qloc = mkLoc n1 m1 1 0 in
  { loc; it = Quoted { qloc; data; kind }}
let parens t =
  let loc = mkLoc (t.loc.source_start-1) (t.loc.source_stop+1) 1 0 in
  mkParens loc t

let ct ?(bug=false) n ?len s =
  let len = match len with None -> String.length s | Some x -> x in
  { TypeExpression.tloc = (mkLoc (n -1 ) (n + len - 1) 1 0); tit = TypeExpression.TConst (Func.from_string s) }
  
let underscore ?bug ?(len=1)n = c ?bug ~len n Func.(show dummyname)

let minl = List.fold_left (fun n x -> min n x.loc.source_start) max_int
let maxl = List.fold_left (fun n x -> max n x.loc.source_stop) min_int
let app a ?(len=String.length a) n ?(parenl=false) ?(parenr=0) ?(bug=false) b =
  let c = c n ~len a in
  let a1 = minl (c :: b) + (if parenl then -1 else 0) in
  let b2 = maxl (c :: b) + (parenr) in
  (* Printf.eprintf "%s a1=%d\n" a a1; *)
  mkApp (mkLoc a1 b2 1 0) (c :: b)

let cast n m t ty = mkCast (mkLoc n m 1 0) t ty

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
let bug = false

let _ =
  (*    01234567890123456789012345 *)
  test  "p :- q."           1 6  1 0 [] ((c 0 "p" |- 3) (c 5 "q"));
  test  "p:- q."            1 5  1 0 [] ((c 0 "p" |- 2) (c 4 "q"));
  test  " p :- q."          2 7  1 0 [] ((c 1 "p" |- 4) (c 6 "q"));
  test  " p  :- q."         2 8  1 0 [] ((c 1 "p" |- 5) (c 7 "q"));
  (*    01234567890123456789012345 *)
  test  "p :- q r."         1 8  1 0 [] ((c 0 "p" |- 3) @@ app "q" 5 [c 7 "r"]);
  test  "p :- ! , q."       1 10 1 0 [] ((c 0 "p" |- 3) @@ app "," 7 [c 5 "!"; c 9 "q"]);
  test  "p :- !, q."        1 9  1 0 [] ((c 0 "p" |- 3) @@ app "," 6 [c 5 "!"; c 8 "q"]);
  test  "p :- q r s."       1 10 1 0 [] ((c 0 "p" |- 3) @@ app "q" 5 [c 7 "r";c 9 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- x \\ q r."    1 12 1 0 [] ((c 0 "p" |- 3) @@ lam "x" 6 (app "q" 9 [c 11 "r"]));
  test  "p :- _ \\ q r."    1 12 1 0 [] ((c 0 "p" |- 3) @@ lam "%dummy" 6 (app "q" 9 [c 11 "r"]));
  test  "(A ; B) :- A."     1 12 1 0 [] ((app ";" 3 [c 1 "A";c 5 "B"] |- 9)~parenl:true @@ c 11 "A");
  (*    01234567890123456789012345 *)
  test  "p :- pi x \\ q."   1 13 1 0 [] ((c 0 "p" |- 3) @@ app "pi" 5 [lam "x" 9 (c 12 "q")]);
  test  "p :- q, r."        1 9  1 0 [] ((c 0 "p" |- 3) @@ app "," 6 [c 5 "q";c 8 "r"]);
  test  "p :- f q, r."      1 11 1 0 [] ((c 0 "p" |- 3) @@ app "," 8 [app "f" 5 [c 7 "q"];c 10 "r"]);
  test  "p :- q, r, s."     1 12 1 0 [] ((c 0 "p" |- 3) @@ app "," 6 [c 5 "q"; c 8 "r"; c 11 "s"]);
  (*    01234567890123456789012345 *)
  test  "p :- q + r * s."   1 14 1 0 [] ((c 0 "p" |- 3) @@ app "+" 7 [c 5 "q"; app "*" 11 [c 9 "r";c 13 "s"]]);
  test  "p :- q + r , s."   1 14 1 0 [] ((c 0 "p" |- 3) @@ app "," 11 [app "+" 7 [c 5 "q";c 9 "r"]; c 13 "s"]);
  test  "p :- q && r = s."  1 15 1 0 [] ((c 0 "p" |- 3) @@ app "=" 12 [app "&&" 7 [c 5 "q"; c 10 "r"]; c 14 "s"]);
  test  "q && r x || s."    1 13 1 0 [] (app "||" 9 [app "&&" 2 [c 0 "q"; app "r" 5 [c 7 "x"]]; c 12 "s"]);
  (*    01234567890123456789012345 *)
  test  "f x ==> y."        1 9 1 0 []  (app "=>" ~len:3 4 [app "f" 0 [c 2 "x"]; c 8 "y"]);
  test  "x, y ==> z, a."    1 13 1 0 [] (app "," 0 [c 0 "x"; app "=>" ~len:3 5 [c 3 "y"; app "," 10 [c 9 "z";c 12 "a"]]]);
  test  "(x, y) ==> z, a."  1 15 1 0 [] (app "=>" ~parenl:true ~len:3 7 [app "," 2 [c 1 "x"; c 4 "y"]; app "," 12 [c 11 "z";c 14 "a"]]);
  test  "x ==> y, z."       1 10 1 0 []  (app "=>" ~len:3 2 [c 0 "x"; app "," 7 [c 6 "y"; c 9 "z"]]);
  test  "x => y, z."        1 9 1 0 [] ~warns:".*infix operator" (app "," 6 [app "=>" 2 [c 0 "x";c 5 "y"];c 8 "z"]);
  test  "x => y, !."        1 9 1 0 [] (app "," 6 [app "=>" 2 [c 0 "x";c 5 "y"];c 8 "!"]);
  test  "(x => y), z."      1 11 1 0 [] (app "," 8 [parens @@ app "=>" 3 [c 1 "x";c 6 "y"];c 10 "z"]);
  test  "x => (y, z)."      1 11 1 0 [] (app "=>" 2 ~parenr:1 [c 0 "x"; app "," 7 [c 6 "y"; c 9 "z"]]);
  (*    01234567890123456789012345 *)
  test  "p :- !, (s X) = X, q." 1 20 1 0 [] ((c 0 "p" |- 3) @@ app "," 6 [c 5 "!";app "="  ~parenl:true  14 [app "s" 9 [c 11 "X"]; c 16  "X"]; c 19 "q"]);
  test  "p :- [ ]."         1 8  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 8 [mkNil 5 ~len:3]);
  test  "p :- []."          1 7  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 7 [mkNil 5]);
  test  "name."             1 4  1 0 [] (c 0 "name");
  test  "p :- a => b => c." 1 16 1 0 [] (app ":-" 2 [c 0 "p";app "=>" 7 [c 5 "a";app "=>" 12 [c 10 "b";c 15 "c"]]]); 
  (*    01234567890123456789012345 *)
  test  "p :- [ a , b ]."   1 14  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 14 [c 7 "a";c 11 "b";mkNil 13 ~len:1]);
  test  "p :- [a,b]."       1 10  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 10 [c 6 "a";c 8 "b";mkNil 9 ~len:1]);
  test  "p :- [ a , {b} ]." 1 16  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 16 [c 7 "a";spill 11 14 (c 12 "b");mkNil 15 ~len:1]);
  test  "p :- [a,{b}]."     1 12  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 12 [c 6 "a";spill 8 11 (c 9 "b");mkNil 11 ~len:1]);
  (*    01234567890123456789012345 *)
  test  "p :- [(a + b)]."   1 14  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 14 [app "+" 9 [c 7 "a";c 11 "b"];mkNil 13 ~len:1]);
  test  "p :- [a + b]."     1 12  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 12 [app "+" 8 [c 6 "a";c 10 "b"];mkNil 11 ~len:1]);
  test  "p :- [ f a , b ]." 1 16  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 16 [app "f" 7 [c 9 "a"];c 13 "b";mkNil 15 ~len:1]);
  test  "p :- [f a,b]."     1 12  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 12 [app "f" 6 [c 8 "a"];c 10 "b";mkNil 11 ~len:1]);
  (*    01234567890123456789012345 *)
  test  "p :- [(a,b)]."     1 12  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 12 [app "," 8 [c 7 "a";c 9 "b"];mkNil 11 ~len:1]);
  test  "p :- [a,b|c]."     1 12  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 12 [c 6 "a";c 8 "b";c 10 "c"]);
  test  "p :- [ a , b \\ @f , x \\ b ]." 1 27  1 0 [] ((c 0 "p" |- 3) @@ mkSeq 5 27 [c 7 "a"; lam "b" 12 (app "," 18 [ c 15 "@f"; lam "x" 21  (c 24 "b")]);mkNil 26 ~len:1]);
  (*    0123456789012345678901234567890 *)
  test  "X is a."           1 6  1 0 [] (app "is" 2 [c 0 "X";c 5 "a"]);
  testF "p :- f use_sig."   14 ".*term expected";
  testF "X is ."            6 ".*expects a right hand side";
  testF "X + ."             5 ".*expects a right hand side";
  testF "X * ."             5 ".*expects a right hand side";
  test  "p :- X is a, Y is b." 1 19 1 0 [] (app ":-" 2 [c 0 "p"; app "," 11 [app "is" 7 [c 5 "X";c 10 "a"];app "is" 15 [c 13 "Y";c 18 "b"]]]);
  (*    0123456789012345678901234567890 *)
  test  "p (f x\\ _ as y)." 1 15 1 0 [] (app "p" 0 [app"as" ~parenl:true ~parenr:1 10 [app "f" 3 [lam "x" 6  (underscore 8)]; c 13 "y"]]); (* parenl implied by bug *)
  (*    01234567890123456789012345 *)
  testF ":-"                2 "unexpected start";
  testF "type ( -> :-"      12 ".*parenthesis.*expected";
  testF "+"                 1 "unexpected start";
  testF "x. x)"             5 "unexpected keyword";
  testF "x. x]"             5 "unexpected keyword";
  testF "x. +"              4 "unexpected start";
  (*    01234567890123456789012345 *)
  test  ":name \"x\" x."    1 11 1 0 [Name "x"] (c 10 "x");
  testT ":index (1) \"foobar\" pred x." ();
  testT ":index (1) pred x."     ();
  testF "p :- g (f x) \\ y." 13 ".*bind.*must follow.*name.*";
  testF "foo i:term, o:term. foo A B :- A = [B]." 6 "unexpected keyword";
  (*    01234567890123456789012345 *)
  testF ":nam \"x\" x."     4 "attribute expected";
  testR "rule p (q r)."     1 12 1 0 [] [ss 5 1 (c 5 "p");ss 7 5 (app "q" 8 [c 10 "r"])] [] None None;
  testR "rule (E :> G ?- r)." 1 18 1 0 [] [s (c 6 "E") (c 11 "G") (c 16  "r")] [] None None;
  test  "p :- f \".*\\\\.aux\"." 1 17 1 0 [] (app ":-" 2 [c 0 "p";app "f" 5  [str 7 17 ".*\\.aux"]]);
  test  "p :- (f x : y)."   1 14 1 0 [] (app ":-" 2 [c 0 "p"; cast 5 14 (app "f" 6 [c 8 "x"]) (ct 13 "y")]);
  test  "p :- pi x : y \\ z."   1 17 1 0 [] (app ":-" 2 [c 0 "p"; app "pi" 5 [lam "x" 9 ~ty:(ct 13 "y") (c 16  "z")]]);
  (*     01234567890123456789012345 *)
  test  "p :- f (x : y)."   1 14 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [cast 7 14 (c 8 "x") (ct 13 "y")]]);
  test  "p :- f (x : y \\ z)." 1 18 1 0 [] (app ":-" 2 [c 0 "p"; app ~parenr:1 "f" 5 [lam "x" 9 ~ty:(ct 13 "y") (c 16 "z")]]);
  test  "p :- f (x : y \\ z as Y)." 1 23 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [app "as" ~parenl:true ~parenr:1 18 [lam "x" 9 ~ty:(ct 13 "y") (c 16 "z"); c 21 "Y"]]]);
  (*    01234567890123456789012345 *)
  testT "func x int, int -> bool, bool."          ();
  testT "func x int, list int -> bool."           ();
  testT "type x (func int, list int -> bool)."           ();
  testT "func x int, (func int -> int) -> bool."  ();
  (*    01234567890123456789012345 *)
  test  "p :- f {{{ g }}}."    1 16 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [q 7 16 10 13 " g "]]);
  test  "p :- f {{ g }}."      1 14 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [q 7 14 9 12 " g "]]);
  test  "p :- f {{:k g }}."    1 16 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [q 7 16 12 14 ~kind:"k" "g "]]);
  test  "p :- f {{{:k g }}}."  1 18 1 0 [] (app ":-" 2 [c 0 "p"; app "f" 5 [q 7 18 13 15 ~kind:"k" "g "]]);
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
    let tok = Lexer.token Elpi_util.Util.StrMap.empty (Lexing.from_string start) in
    let token = mk_token start in
    assert(tok = token);
    begin try match fixity with
    | Infix | Infixl | Infixr ->
        ignore(Parser.Internal.infix_SYMB Lexer.(token Elpi_util.Util.StrMap.empty) (Lexing.from_string start))
    | Postfix ->
        ignore(Parser.Internal.postfix_SYMB Lexer.(token Elpi_util.Util.StrMap.empty) (Lexing.from_string start))
    | Prefix ->
        ignore(Parser.Internal.prefix_SYMB Lexer.(token Elpi_util.Util.StrMap.empty) (Lexing.from_string start))
    with _ ->
      Printf.eprintf "\n           (*          1         2         3 *)";
      Printf.eprintf "\n           (* 123456789012345678901234567890 *)";
      Printf.eprintf "\nerror parsing %s\n" start;
      exit 1
    end;
    begin match enclose with
    | None -> ()
    | Some f ->
      let v = f "xx" in
      assert(CONSTANT v = Lexer.token Elpi_util.Util.StrMap.empty (Lexing.from_string v));
    end;
    x) tokens) |> List.concat |> List.length in
  assert(extensible_SYMB = 14)

