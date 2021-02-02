(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "sepcomp1"
  ~source_dune:"sepcomp1.ml"
  ~description:"simple separate compilation"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()

let () = declare "sepcomp2"
  ~source_dune:"sepcomp2.ml"
  ~description:"simple separate compilation"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()

let () = declare "sepcomp3"
  ~source_dune:"sepcomp3.ml"
  ~description:"separate compilation double naming"
  ~expectation:Test.(FailureOutput (Str.regexp "a clause named xxx already exists"))
  ()

let () = declare "sepcomp4"
  ~source_dune:"sepcomp4.ml"
  ~description:"separate compilation double naming"
  ~expectation:Test.(FailureOutput (Str.regexp "uplicate mode declaration for p"))
  ()

let () = declare "sepcomp5"
  ~source_dune:"sepcomp5.ml"
  ~description:"separate compilation different processes (step 1)"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp6"
  ~source_dune:"sepcomp6.ml"
  ~after:"sepcomp5"
  ~description:"separate compilation different processes (step 2)"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()


let () = declare "sepcomp_perf"
  ~source_dune:"sepcomp_perf.ml"
  ~after:"sepcomp_perf"
  ~description:"separate compilation perf"
  ~expectation:Test.Success
  ()
