(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))


let () = declare "grundlagen"
  ~source_elpi:"helena_elpi/ld3_engine.elpi"
  ~description:"type checker for λδ"
  ()

let () = declare "lyp"
  ~source_elpi:"lyp/lyp_engine.elpi"
  ~description:"type checker for λΥP"
  ()

let () = declare "cbv"
  ~source_elpi:"reduce_cbv.elpi"
  ~source_teyjus:"reduce_cbv.mod"
  ~description:"reduction"
  ()
let () = declare "cbn"
  ~source_elpi:"reduce_cbn.elpi"
  ~source_teyjus:"reduce_cbn.mod"
  ~description:"reduction"
  ()

let () = declare "lambda3"
  ~source_elpi:"lambda3.elpi"
  ~source_teyjus:"lambda3.mod"
  ~description:"moving under lambdas"
  ()
