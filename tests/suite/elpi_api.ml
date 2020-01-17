(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "sepcomp1"
  ~source_dune:"sepcomp1.ml"
  ~description:"simple separate compilation"
  ~expectation:Test.(Output (Str.regexp "ok"))
  ()

let () = declare "sepcomp2"
  ~source_dune:"sepcomp2.ml"
  ~description:"simple separate compilation"
  ~expectation:Test.(Output (Str.regexp "ok"))
  ()

let () = declare "sepcomp3"
  ~source_dune:"sepcomp3.ml"
  ~description:"separate compilation double naming"
  ~expectation:Test.(Output (Str.regexp "a clause named xxx already exists"))
  ()

let () = declare "sepcomp4"
  ~source_dune:"sepcomp4.ml"
  ~description:"separate compilation double naming"
  ~expectation:Test.(Output (Str.regexp "uplicate mode declaration for p"))
  ()

let () = declare "sepcomp5"
  ~source_dune:"sepcomp5.ml"
  ~description:"separate compilation double naming"
  ~expectation:Test.(Output (Str.regexp "ok"))
  ()
