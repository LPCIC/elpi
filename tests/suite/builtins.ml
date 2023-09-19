(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Suite

let declare = Test.declare
    ~category:(Filename.(chop_extension (basename __FILE__)))

let () = declare "name"
  ~source_elpi:"name_builtin.elpi"
  ~description:"name builtin"
  ~typecheck:false
  ()
let () = declare "nil_cons"
  ~source_elpi:"nil_cons.elpi"
  ~description:"nil = []"
  ()

let () = declare "random"
  ~source_elpi:"random.elpi"
  ~description:"random numbers"
  ()

let () = declare "findall"
  ~source_elpi:"findall.elpi"
  ~description:"stash across backtrack"
  ()

let () =
  let v = Sys.ocaml_version in
  if Str.string_match (Str.regexp "4\\.\\(08\\|09\\|10\\|11\\12|\\)") v 0 then
    () (* unix opem_process_* APIS are broken *)
  else
    declare "unix"
      ~source_elpi:"unix.elpi"
      ~description:"unix APIs"
      ()
