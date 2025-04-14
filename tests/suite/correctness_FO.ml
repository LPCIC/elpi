(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "pm"
  ~source_elpi:"pm.elpi"
  ~description:"pattern matching builtin"
  ()

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

let () = declare "macro_type"
  ~source_elpi:"macro_type.elpi"
  ~description:"polymorphic macro"
  ()

let () = declare "macro_type_err_pos"
  ~source_elpi:"macro_type_err_pos.elpi"
  ~description:"polymorphic macro"
  ~expectation:(FailureOutput (Str.regexp "line 5, column 8.*\nTypechecker"))
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

let () = 
  let sample = Filename.get_temp_dir_name () ^ Filename.dir_sep ^ "dt_empty_list.log" in
  declare "dt_empty_list"
  ~source_elpi:"dt_empty_list.elpi"
  ~description:"discrimination_tree empty_list"
    ~trace:(On["tty";"file://"^sample;"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:[^l]"])
  ~expectation:(SuccessOutputFile { sample; adjust = Util.strip_cwd; reference = "dt_empty_list.log" })
  ()

let () = declare "dt_var2"
  ~source_elpi:"dt_var2.elpi"
  ~description:"discrimination_tree indexing flex"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 3"))
  ()

let () = declare "dt_var3"
  ~source_elpi:"dt_var3.elpi"
  ~description:"discrimination_tree indexing flex"
    ~trace:(On["tty";"stdout";"-trace-at";"1";"9999";"-trace-only";"dev:disc-tree:candidates"])
  ~expectation:(SuccessOutput (Str.regexp "dev:disc-tree:candidates = 2"))
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

let () =
  let (!) x = Test.FailureOutput (Str.regexp x) in
  let mut_excl l1 l2 = !(Format.asprintf "line %d.*\n.*\n+.*line %d" l1 l2) in
  let det_check l c = !(Format.asprintf "line %d, column %d.*\nDetCheck.*relational atom" l c) in
  let out_err l c = !(Format.asprintf "line %d, column %d.*\nDetCheck.*output" l c) in
  let mode_err l c = !(Format.asprintf "line %d, column %d.*\nTypechecker.*[io]:.*" l c) in
  let status = Test.
    [|(*01*) mut_excl 9 6; Success; det_check 9 7; Success; Failure;            (*05*)
      (*06*) Success; Failure; Failure; Failure; Failure;                       (*10*)
      (*11*) mut_excl 9 8; Success; mut_excl 11 10; det_check 21 9; Success;    (*15*)
      (*16*) det_check 8 9; Success; det_check 14 7; det_check 13 7; Success;         (*20*)
      (*21*) det_check 7 21; Success; det_check 16 9; Success; det_check 7 12;  (*25*)
      (*26*) mut_excl 13 10; mut_excl 12 10; Success; Success; det_check 8 7;   (*30*)
      (*31*) out_err 7 10; Success; out_err 10 14; out_err 9 21; out_err 9 13;  (*35*)
      (*36*) Success; out_err 6 10; out_err 7 3; Success; Success;              (*40*)
      (*41*) det_check 6 21; out_err 7 4; out_err 5 4; Success; det_check 11 34;(*45*)
      (*46*) Success; Success; Success; Success; det_check 8 16;                (*50*)
      (*51*) Success; det_check 19 2; Success; out_err 8 4; Success;            (*55*)
      (*56*) det_check 10 2; out_err 12 19; out_err 13 8; Success; Success;     (*60*)
      (*61*) det_check 12 2; Success; Success; Success; det_check 10 2;          (*65*)
      (*66*) Success; det_check 9 31; det_check 11 5; det_check 7 39; det_check 2 21; (*70*)
      (*71*) Success; Success; out_err 10 5; out_err 8 4; det_check 17 5;
      (*76*) Success; Success; det_check 7 5; Success; Success;                 (*80*)
      (*81*) mode_err 13 6; Success; mode_err 15 6; Success; mode_err 14 26;    (*85*)
      (*86*) Success; Success; Success; Success; Success;                       (*90*)
      (*91*) det_check 14 5; Success; Success; det_check 14 5; Success;         (*95*)
      (*96*) mut_excl 6 6
    |] in
  let ignore = [7;8;9;10;27] in
  for i = 0 to Array.length status - 1 do
    if not (List.mem (i+1) ignore) then (
    let name = Printf.sprintf "functionality/test%d.elpi" (i+1) in
    let descr = Printf.sprintf "functionality%d" (i+1) in
    declare descr
    ~source_elpi:name
    ~description:descr
    ~expectation:status.(i)
    ())
  done


let () = declare "sepcomp_tyid"
  ~source_dune:"sepcomp_tyid.exe"
  ~after:"sepcomp_tyid"
  ~description:"separate compilation union find on type_id"
  ~expectation:Test.Success
  ()