let file_name = Sys.argv.(1)

(* Attributes and directives that are not exercised by the other tests *)

open Elpi.API

let declaration = PPX.empty_declaration ()

(* The documentation of the type, and the readback of the terms that are not a
   constructor *)
type color = Red | Green | Blue of int
[@@elpi.type_doc "The colours"]
[@@elpi.default_constructor_readback
   (fun _default ~depth _ _ state _ -> state, Red, [])]
[@@deriving show, elpi { declaration }]

(* The Elpi name of a constructor and its documentation, a constructor not
   exposed to Elpi *)
type shape =
  | Circle of int [@elpi.code "round"] [@elpi.doc "A circle"]
  | Square of int
  | Hidden of color [@elpi.skip]
[@@deriving show, elpi { declaration }]

(* The Elpi name of the type, and the deep copy of lists and of the other
   containers, whose elements have a copy function (here the ones of the types
   above) *)
type nested = N of shape list option * (int * color list)
[@@elpi.type_code "nest"]
[@@deriving show, elpi { declaration }]

(* The conversion of a type, as an expression *)
let colors :
    (color list, PPX.ctx, Data.constraints)
      ContextualConversion.t =
  [%elpi: color list]

let builtin =
  BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
