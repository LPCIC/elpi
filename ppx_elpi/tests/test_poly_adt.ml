let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type 'a simple = A | B of int | C of 'a list * int
[@@deriving show, elpi { declaration } ]

let simple :
    'a 'c 'csts.
    ('a, #PPX.ctx as 'c, 'csts)
      ContextualConversion.t ->
    ('a simple, #PPX.ctx as 'c, 'csts)
      ContextualConversion.t = simple

(* in the base context *)
let t2 :
    (int simple, PPX.ctx,
       Data.constraints)
      ContextualConversion.t =
  simple BuiltInData.intC

(* a context with more than what is needed by simple *)
class type my_context_subclass = object
  inherit PPX.ctx
  method foobar : bool
end

let t3 :
    (float simple, my_context_subclass,
       Data.constraints)
      ContextualConversion.t =
  simple BuiltInData.floatC

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
