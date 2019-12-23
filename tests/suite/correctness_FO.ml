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
