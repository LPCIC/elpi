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
