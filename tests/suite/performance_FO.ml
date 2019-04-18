(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "crypt"
  ~source_elpi:"crypt.elpi"
  ~source_teyjus:"crypt.mod"
  ~description:"standard Prolog benchmark"
  ()

let () = declare "queens"
  ~source_elpi:"queens.elpi"
  ~source_teyjus:"queens.mod"
  ~description:"standard Prolog benchmark"
  () 

let () = declare "rev14"
  ~source_elpi:"rev14.elpi"
  ~source_teyjus:"rev14.mod"
  ~description:"list reversal"
  ()

let () = declare "mu"
  ~source_elpi:"mu.elpi"
  ~source_teyjus:"mu.mod"
  ~description:"standard Prolog benchmark"
  () 

let () = declare "zebra"
  ~source_elpi:"zebra.elpi"
  ~source_teyjus:"zebra.mod"
  ~description:"standard Prolog benchmark"
  () 

let () = declare "fast_mu"
  ~source_elpi:"fast_mu.elpi"
  ~source_teyjus:"fast_mu.mod"
  ~description:"standard Prolog benchmark"
  () 

let () = declare "rev"
  ~source_elpi:"rev.elpi"
  ~description:"list reversal"
  ()

let () = declare "ackermann"
  ~source_elpi:"ackermann.elpi"
  ~description:"ackermann"
  ()

let () = declare "index2"
  ~source_elpi:"index2.elpi"
  ~description:"indexing the second argument"
  ()

let () = declare "deep_index"
  ~source_elpi:"deep_indexing.elpi"
  ~description:"indexing deeper rules out"
  ()
