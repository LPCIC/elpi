(* The passes of the compiler do not stop at the first error: each unit of
   work (a rule, a type, ...) that is wrong is dropped and its error is
   returned, together with the name of the pass that found it. *)
open Elpi.API

let src = {|
pred p i:int.
:name "a" :name "b" p 0.
p X :- @nomacro X.
p "s".
func f int -> int.
f X Y :- p X, Y = 1.
p 2.
type foo int -> bar.
}
main.
|}

(* (component, line, a part of the message) in the order of the passes *)
let expected = [
  "Structure", 3, "duplicate attribute name";
  "Structure", 10, "extra }";
  "Scope", 4, "Unknown macro @nomacro";
  "Typechecker", 9, "Unknown type bar";
  "Typechecker", 5, "has type string but p expects an argument of type int";
  "DetCheck", 7, "Found relational atom (p X)";
]

let contains s sub =
  let n = String.length sub in
  let rec go i = i + n <= String.length s && (String.sub s i n = sub || go (i+1)) in
  go 0

let line_of src { Ast.Loc.source_start; _ } =
  let n = ref 1 in
  String.iteri (fun i c -> if i < source_start && c = '\n' then incr n) src;
  !n

(* the errors, and the lines of the symbols of the rules of the unit *)
let compile src =
  let max_errors = 100 in
  let elpi = Sepcomp.Sepcomp_template.init () in
  let flags = { Compile.default_flags with Compile.max_errors } in
  let ast, parse_errors = Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial "src") ~digest:(Digest.string src) (Lexing.from_string src) in
  assert (parse_errors = []);
  let sps, e0 = Compile.scope_ast ~elpi ~flags ast in
  let _, errors, lines =
    List.fold_left (fun (base, errors, lines) sp ->
      let u, e1 = Compile.unit ~elpi ~flags ~base sp in
      let base, e2 = Compile.extend ~flags ~base u in
      let lines = ref lines in
      Compile.iter sp u (fun n -> lines := line_of src n.Compile.loc :: !lines);
      base, errors @ e1 @ e2, !lines) (Compile.empty_base ~elpi, e0, []) sps in
  errors, lines

let () =
  let errors, lines = compile src in
  let actual = List.map (fun { Compile.component; loc; message } ->
    component, (match loc with Some l -> line_of src l | None -> 0), message) errors in
  let ok = List.length actual = List.length expected &&
    List.for_all2 (fun (c, l, m) (c', l', m') -> c = c' && l = l' && contains m' m) expected actual in
  if not ok then begin
    List.iter (fun e -> Format.eprintf "%a@." Compile.pp_error e) errors;
    prerr_endline "unexpected errors";
    exit 1
  end;
  (* what is wrong is not in the unit, what is not is: the rule at line 3 has
     a duplicate attribute, the one at line 4 an unknown macro, the one at line 5
     a type error; the one at line 7 fails the determinacy check only; the
     one at line 8 is fine *)
  let has l = List.mem l lines in
  if has 3 || has 4 || has 5 || not (has 7) || not (has 8) then begin
    prerr_endline "wrong rules in the unit";
    exit 1
  end;
  (* the limit (of each pass): the errors up to it, then one saying that the
     rest was not checked *)
  let elpi = Sepcomp.Sepcomp_template.init () in
  let flags = { Compile.default_flags with Compile.max_errors = 2 } in
  let ast, _ = Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial "src") ~digest:(Digest.string src) (Lexing.from_string src) in
  let _, errors = Compile.scope_ast ~elpi ~flags ast in
  (match List.rev errors with
   | { Compile.component = "Compiler"; message; _ } :: rest when contains message "too many errors" && List.length rest = 2 -> ()
   | _ ->
       List.iter (fun e -> Format.eprintf "%a@." Compile.pp_error e) errors;
       prerr_endline "max_errors";
       exit 1);
  (* max_errors = 0: the first error is raised *)
  let flags = { Compile.default_flags with Compile.max_errors = 0 } in
  let elpi = Sepcomp.Sepcomp_template.init () in
  (match Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial "src") ~digest:(Digest.string "") (Lexing.from_string "p :- . q.") with
   | _ -> prerr_endline "parse error not raised"; exit 1
   | exception Parse.ParseError _ -> ());
  let ast, _ = Parse.program_from ~elpi ~loc:(Ast.Loc.initial "src") ~digest:(Digest.string src) (Lexing.from_string src) in
  (match Compile.scope_ast ~elpi ~flags ast with
   | _ -> prerr_endline "compile error not raised"; exit 1
   | exception Compile.CompileError { Compile.component = "Structure"; message; _ } when contains message "duplicate attribute" -> ());
  exit 0
