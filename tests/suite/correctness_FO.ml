(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "cut1"
  ~source_elpi:"cut.elpi"
  ~description:"what else"
  ()
let () = declare "cut2"
  ~source_elpi:"cut2.elpi"
  ~description:"what else"
  ()
let () = declare "cut3"
  ~source_elpi:"cut3.elpi"
  ~description:"what else"
  ()
let () = declare "cut4"
  ~source_elpi:"cut4.elpi"
  ~description:"what else"
  ()
let () = declare "cut5"
  ~source_elpi:"cut5.elpi"
  ~description:"what else"
  ()
let () = declare "cut6"
  ~source_elpi:"cut6.elpi"
  ~description:"what else"
  ()

let () = declare "backtracking"
  ~source_elpi:"trail.elpi"
  ~description:"backtracking variable assignment"
  ()

let () = declare "uminus"
  ~source_elpi:"uminus.elpi"
  ~description:"parsing and evaluation of unary minus"
  ()

let () = declare "typeabbrv1"
  ~source_elpi:"typeabbrv1.elpi"
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv2"
  ~source_elpi:"typeabbrv2.elpi"
  ~expectation:Failure
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv3"
  ~source_elpi:"typeabbrv3.elpi"
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv4"
  ~source_elpi:"typeabbrv4.elpi"
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv5"
  ~source_elpi:"typeabbrv5.elpi"
  ~expectation:Failure
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv6"
  ~source_elpi:"typeabbrv6.elpi"
  ~expectation:Failure
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv7"
  ~source_elpi:"typeabbrv7.elpi"
  ~expectation:Success
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv8"
  ~source_elpi:"typeabbrv8.elpi"
  ~expectation:Success
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv9"
  ~source_elpi:"typeabbrv9.elpi"
  ~expectation:Success
  ~description:"type abbreviations"
  ()
let () = declare "typeabbrv10"
  ~source_elpi:"typeabbrv10.elpi"
  ~expectation:(FailureOutput (Str.regexp "literal.*3.*expects a term of type list A"))
  ~description:"type abbreviations and error messages"
  ()
let () = declare "typeabbrv11"
  ~source_elpi:"typeabbrv11.elpi"
  ~expectation:(FailureOutput (Str.regexp "has type string but f expects a term of type x"))
  ~description:"type abbreviations and error messages"
  ()
let () = declare "typeabbrv12"
  ~source_elpi:"typeabbrv12.elpi"
  ~expectation:(FailureOutput (Str.regexp "has type string but f expects a term of type y"))
  ~description:"type abbreviations and error messages"
  ()

let () = declare "typeabbrv13"
  ~source_elpi:"typeabbrv13.elpi"
  ~description:"type abbreviations"
  ()

(* let () = declare "typeabbrv14"
  ~source_elpi:"typeabbrv14.elpi"
  ~description:"type abbreviations"
  ~expectation:(FailureOutput (Str.regexp "SYMBOL.*uses the undefined dl constant"))
  () *)

let () = declare "conj2"
  ~source_elpi:"conj2.elpi"
  ~description:"parsing and evaluation of & (binary conj)"
  ()

(* 
  Note in the following tests with DT, we disable typecheck not to print the
  number of candidates found in the search of clauses done by the elpi typechecker
*)
let () = declare "dt_var"
  ~source_elpi:"dt_var.elpi"
  ~description:"discrimination_tree indexing flex"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 2"))
  ()

let () = 
  let sample = Filename.get_temp_dir_name () ^ Filename.dir_sep ^ "dt_max_depths.log" in
  declare "dt_max_depths"
  ~source_elpi:"dt_max_depths.elpi"
  ~description:"discrimination_tree max_depth"
    ~trace:(On["tty";"file://"^sample;"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:depth-path"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "dt_max_depths.log" })
  ()

let () = declare "dt_var2"
  ~source_elpi:"dt_var2.elpi"
  ~description:"discrimination_tree indexing flex"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 3"))
  ()

let () = declare "dt_multiparam1"
  ~source_elpi:"dt_multiparam1.elpi"
  ~description:"discrimination_tree indexing multi argument"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 1"))
  ()

let () = declare "dt_multiparam2"
  ~source_elpi:"dt_multiparam2.elpi"
  ~description:"discrimination_tree indexing multi with flexible"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 101"))
  ()

let () = declare "dt_multiparam3"
  ~source_elpi:"dt_multiparam3.elpi"
  ~description:"discrimination_tree indexing multi with flexible in input mode"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(FailureOutput (Str.regexp "dev:disc-tree:candidates = 0"))
  ()

let () = declare "dt_multivar"
  ~source_elpi:"dt_multivar.elpi"
  ~description:"discrimination_tree indexing multi with flexible in input mode"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (
      let wanted_length = [5;1;0;1;1;5;4;5;2;5;4;5;6;1] in
      let all_char = "\\(.\\|\n\\)*" in
      let s = List.fold_left (fun acc e -> Printf.sprintf "%s = %d%s" acc e all_char) "" wanted_length in
      Str.regexp s))
  ()

let () = declare "is"
  ~source_elpi:"is.elpi"
  ~description:"calc"
  ()

let () = declare "trie"
  ~source_elpi:"trie.elpi"
  ~description:"discrimination_tree on trees"
  ()

let mode_check expected fname =
  let is_in_file = Util.has_substring ~sub:fname in
  let start_warning = String.starts_with ~prefix:"WARNING" in
  let pos = ref 0 in
  let check_same x =
    let res = try Str.(search_forward (regexp expected.(!pos))) x 0 |> ignore; true
              with Not_found -> false in
    if not res then Printf.eprintf "Expected [[%s]]; \nFound    [[%s]]\n" expected.(!pos) x;
    incr pos; 
    res in
  let rec f = function
    | [] | [_] -> true
    | x :: x' :: xs when start_warning x && is_in_file x' ->
      check_same x && f xs
    | x :: x' :: x'' :: xs when start_warning x && is_in_file x'' ->
      check_same x && check_same x' && f xs
    | _ :: xs -> f xs in
    f

let () = declare "mode_checking_fo"
  ~source_elpi:"mode_checking_fo.elpi"
  ~description:"mode_checking_fo"
  ~expectation:(SuccessOutputTxt (
    let expected = [|
      "WARNING: Not ground Y passed to p "; 
      "WARNING: The variables \\[Y\\] are in output position of the predicate\" "; 
      "\"and cannot be ensured to be ground "|] in
    mode_check expected "mode_checking_fo"
    ))
  ()

let () = declare "mode_checking_ho"
  ~source_elpi:"mode_checking_ho.elpi"
  ~description:"mode_checking_ho"
  ~expectation:(SuccessOutputTxt (
    let expected = [|
      "WARNING: Not ground Z passed to p "; 
      "WARNING: Not ground (con Z) passed to p ";
      "WARNING: Not ground X[0-9]+ c[0-9]+ passed to p ";
      "WARNING: Passed flexible to , ";
      "WARNING: Not ground C passed to c0 ";
      "WARNING: The variables \\[C\\] are in output position of the predicate\" ";
      "\"and cannot be ensured to be ground "
      |] in
    mode_check expected "mode_checking_ho"
    ))
  ()

let () =
  let status = Test.
    [|Failure; Success; Failure; Success; Failure; (*05*)
      Success; Failure; Failure; Failure; Failure; (*10*)
      Failure; Success; Failure; Failure; Success; (*15*)
      Success; Success; Failure; Failure; Success; (*20*)
      Failure; Success; Failure; Failure; Failure; (*25*)
      Failure; Failure; Success; Success; Failure|] in
  let ignore = [1;5;7;8;9;10;11;13;16;17;20;24;26;27;28;30] in
  (* interesting tests:24 *)
  for i = 0 to -1 (* Array.length status - 1*) do
    if not (List.mem (i+1) ignore) then (
    let name = Printf.sprintf "functionality/test%d.elpi" (i+1) in
    let descr = Printf.sprintf "functionality%d" (i+1) in
    declare descr
    ~source_elpi:name
    ~description:descr
    ~expectation:status.(i)
    ())
  done
