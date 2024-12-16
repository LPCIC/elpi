(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "sepcomp1"
  ~source_dune:"sepcomp1.exe"
  ~description:"simple separate compilation"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()

let () = declare "sepcomp2"
  ~source_dune:"sepcomp2.exe"
  ~description:"simple separate compilation"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()

let () = declare "sepcomp3"
  ~source_dune:"sepcomp3.exe"
  ~description:"separate compilation double naming"
  ~expectation:Test.(FailureOutput (Str.regexp "duplicate clause name xxx"))
  ()

let () = declare "sepcomp4"
  ~source_dune:"sepcomp4.exe"
  ~description:"separate compilation double naming"
  ~expectation:Test.(FailureOutput (Str.regexp "duplicate mode declaration for p"))
  ()

let () = declare "sepcomp5"
  ~source_dune:"sepcomp5.exe"
  ~description:"separate compilation different processes (step 1)"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp6"
  ~source_dune:"sepcomp6.exe"
  ~after:"sepcomp5"
  ~description:"separate compilation different processes (step 2)"
  ~expectation:Test.(SuccessOutput (Str.regexp "ok"))
  ()

  let () = declare "sepcomp7"
  ~source_dune:"sepcomp7.exe"
  ~description:"separate compilation different processes, with remove (step 1)"
  ~expectation:Test.Success
  ()

  let () = declare "sepcomp8"
  ~source_dune:"sepcomp8.exe"
  ~description:"separate compilation different processes, with remove (step 2)"
  ~expectation:Test.Success
  ()

  let () = declare "sepcomp9"
  ~source_dune:"sepcomp9.exe"
  ~description:"separate compilation different processes, with remove (step 3)"
  ~expectation:Test.Success
  ()

