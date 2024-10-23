(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "sepcomp_perf1"
  ~source_dune:"sepcomp_perf1.ml"
  ~after:"sepcomp_perf1"
  ~description:"separate compilation perf"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp_perf2"
  ~source_dune:"sepcomp_perf2.ml"
  ~after:"sepcomp_perf2"
  ~description:"separate compilation linker perf"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp_perf3"
  ~source_dune:"sepcomp_perf3.ml"
  ~after:"sepcomp_perf3"
  ~description:"separate compilation linker perf"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp_perf4"
  ~source_dune:"sepcomp_perf4.ml"
  ~after:"sepcomp_perf4"
  ~description:"separate compilation linker perf"
  ~expectation:Test.Success
  ()

let () = declare "sepcomp_perf5"
  ~source_dune:"sepcomp_perf5.ml"
  ~after:"sepcomp_perf5"
  ~description:"separate compilation linker perf and time distribution"
  ~expectation:Test.Success
  ()
