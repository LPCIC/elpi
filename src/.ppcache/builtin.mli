(*2e0e48bc925828ab0ecba74ffc97af5e3324c92f *src/builtin.mli --cookie elpi_trace="false"*)
#1 "src/builtin.mli"
open API.BuiltIn
val core_builtins : declaration list
val io_builtins : declaration list
val lp_builtins : declaration list
val elpi_builtins : declaration list
val elpi_nonlogical_builtins : declaration list
val elpi_stdlib : declaration list
val elpi_map : declaration list
val elpi_set : declaration list
val ocaml_map :
  name:string ->
    ('a, API.Conversion.ctx) API.Conversion.t ->
      (module API.Utils.Map.S with type key = 'a) -> declaration list
[@@ocaml.doc
  " Easy export of OCaml's Map/Set modules, use as follows:\n   module StrMap = API.Utils.Map.Make(String)\n   ocaml_map ~name:\"strmap\" BuiltInData.string (module StrMap) "]
val ocaml_set :
  name:string ->
    ('a, API.Conversion.ctx) API.Conversion.t ->
      (module API.Utils.Set.S with type elt = 'a) -> declaration list
val std_declarations : declaration list
val std_builtins : API.Setup.builtins
val pair :
  ('a, 'c) API.Conversion.t ->
    ('b, 'c) API.Conversion.t -> (('a * 'b), 'c) API.Conversion.t
val option : ('a, 'c) API.Conversion.t -> ('a option, 'c) API.Conversion.t
val bool : (bool, 'c) API.Conversion.t
val char : (char, 'c) API.Conversion.t
val triple :
  ('a, 'h) API.Conversion.t ->
    ('b, 'h) API.Conversion.t ->
      ('c, 'h) API.Conversion.t -> (('a * 'b * 'c), 'h) API.Conversion.t
val quadruple :
  ('a, 'h) API.Conversion.t ->
    ('b, 'h) API.Conversion.t ->
      ('c, 'h) API.Conversion.t ->
        ('d, 'h) API.Conversion.t ->
          (('a * 'b * 'c * 'd), 'h) API.Conversion.t
val quintuple :
  ('a, 'h) API.Conversion.t ->
    ('b, 'h) API.Conversion.t ->
      ('c, 'h) API.Conversion.t ->
        ('d, 'h) API.Conversion.t ->
          ('e, 'h) API.Conversion.t ->
            (('a * 'b * 'c * 'd * 'e), 'h) API.Conversion.t
type diagnostic = private
  | OK 
  | ERROR of string API.BuiltInPredicate.ioarg 
val diagnostic : (diagnostic, 'c) API.Conversion.t
val mkOK : diagnostic
val mkERROR : string -> diagnostic
val in_stream : ((in_channel * string), 'c) API.Conversion.t
val out_stream : ((out_channel * string), 'c) API.Conversion.t
val default_checker : unit -> API.Compile.program

