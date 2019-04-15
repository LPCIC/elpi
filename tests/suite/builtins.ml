(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "name"
  ~source_elpi:"name_builtin.elpi"
  ~description:"name builtin"
  ()
let () = declare "nil_cons"
  ~source_elpi:"nil_cons.elpi"
  ~description:"nil = []"
  ()

let () = declare "random"
  ~source_elpi:"random.elpi"
  ~description:"random numbers"
  ()

