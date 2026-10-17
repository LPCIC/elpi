let p1 = {|
  p 2 :- p 1.
|}

let maine = {|
pred p o:int.
p 1.
main :- p X, X = X.
|}

open Elpi.API

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let pmain,unit0 = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 1 maine in
  let _,_unit1 = cc ~elpi ~flags ~base:pmain 2 p1 in

  (* the symbols of the unit, found by position *)
  let sp =
    match ok (Compile.scope_ast ~elpi ~flags
      (ok (Parse.program_from ~elpi ~digest:(Digest.string maine) ~loc:(Ast.Loc.initial "<u1>") (Lexing.from_string maine)))) with
    | [x] -> x | _ -> assert false in
  let nodes = ref [] in
  Compile.iter sp unit0 (fun n -> nodes := (n.Compile.loc, n) :: !nodes);
  let tree = Compile.IntervalTree.of_list !nodes in

  let mkloc u n m =
    let l = Ast.Loc.initial (Printf.sprintf "<u%d>" u) in
    { l with Ast.Loc.source_start = n; source_stop = m } in

  let text_of_loc s { Ast.Loc.source_start = n; source_stop = m } =
    String.sub s n (m-n) in

  let find loc = Compile.IntervalTree.find loc tree |> List.map snd in
  let fail msg = Printf.eprintf "sepcomp_hover: %s\n" msg; exit 1 in

  let loc_x = mkloc 1 33 34 in
  let loc_comma = mkloc 1 31 32 in
  let loc_p = mkloc 1 28 29 in
  let loc_pred = mkloc 1 6 16 in
  let loc_head = mkloc 1 28 38 in

  (* X is a variable of the rule: its binder is the head of the rule *)
  (match List.filter (fun n -> n.Compile.kind = Compile.Unification_variable) (find loc_x) with
   | n :: _ ->
       if text_of_loc maine n.Compile.loc <> "X" then fail "X";
       if n.Compile.defined = None then fail "X has no binder"
   | [] -> fail "no variable at X");
  (* , is a keyword *)
  if not (List.exists (fun n -> n.Compile.kind = Compile.Keyword) (find loc_comma)) then fail "no keyword at ,";
  (* p is a predicate declared in this file *)
  (match List.filter (fun n -> match n.Compile.kind with Compile.Constant (Compile.Predicate, Compile.User) -> true | _ -> false) (find loc_p) with
   | n :: _ ->
       if n.Compile.defined = None then fail "p has no declaration"
   | [] -> fail "no predicate at p");
  (* the type expressions of the declarations are visited too *)
  if not (List.exists (fun n -> n.Compile.kind = Compile.Type_constructor) (find (mkloc 1 6 12))) then fail "no type expression";
  ignore (loc_pred, loc_head);
  exit 0
