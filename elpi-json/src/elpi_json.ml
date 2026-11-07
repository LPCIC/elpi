(* elpi-json: Yojson bindings for Elpi, the plugin json of findlib package
   elpi-json (accumulate "+json"). Taken from rocq-elpi's apps/json, without
   its Rocq specific code. *)
open Elpi.API

let declaration = PPX.empty_declaration ()

(* Yojson.Basic.t as an ordinary variant, for ppx_elpi *)
type t =
  | Null
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | Assoc of (string * t) list
      [@elpi.doc "key value pairs. When generated from built-in predicates, keys are sorted"]
  | List of t list
[@@elpi.namespace "json"]
[@@elpi.type_code "json"]
[@@elpi.type_doc "Yojson.Basic.t"]
[@@deriving show, elpi { declaration }]

let rec of_yojson : Yojson.Basic.t -> t = function
  | `Null -> Null
  | `Bool b -> Bool b
  | `Int n -> Int n
  | `Float f -> Float f
  | `String s -> String s
  | `Assoc l ->
      Assoc (List.map (fun (k, v) -> k, of_yojson v) (List.stable_sort (fun (x, _) (y, _) -> String.compare x y) l))
  | `List l -> List (List.map of_yojson l)

let rec to_yojson : t -> Yojson.Basic.t = function
  | Null -> `Null
  | Bool b -> `Bool b
  | Int n -> `Int n
  | Float f -> `Float f
  | String s -> `String s
  | Assoc l -> `Assoc (List.map (fun (k, v) -> k, to_yojson v) l)
  | List l -> `List (List.map to_yojson l)

let json = ContextualConversion.(!<) t

open BuiltIn
open BuiltInPredicate
open BuiltInPredicate.Notation
open BuiltInData
open Elpi.Builtin

let json_from_file = MLCode(Pred("json.from_file",
  In(string,"File",
  Out(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.from_file reads J from File.
If D is error then J is not assigned.|}))),
  (fun f _ _ ~depth:_ ->
    try !: (of_yojson (Yojson.Basic.from_file ~fname:f f)) +! mkOK
    with Yojson.Json_error s | Sys_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_from_string = MLCode(Pred("json.from_string",
  In(string,"String",
  Out(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.from_string reads J from String.
If D is error then J is not assigned.|}))),
  (fun s _ _ ~depth:_ ->
    try !: (of_yojson (Yojson.Basic.from_string s)) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_to_file = MLCode(Pred("json.to_file",
  In(string,"File",
  In(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_file writes J to File.|}))),
  (fun f j _ ~depth:_ ->
    try Yojson.Basic.to_file f (to_yojson j); !: mkOK
    with Yojson.Json_error s | Sys_error s -> !: (mkERROR s))),
  DocAbove)

let json_to_string = MLCode(Pred("json.to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_string writes J to a compact string S.|}))),
  (fun j _ _ ~depth:_ ->
    try !: (Yojson.Basic.to_string ~std:true (to_yojson j)) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_pretty_to_string = MLCode(Pred("json.pretty_to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.pretty_to_string writes J to a nice string S.|}))),
  (fun j _ _ ~depth:_ ->
    try !: (Yojson.Basic.pretty_to_string ~std:true (to_yojson j)) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let builtins : Setup.builtins = Plugin.register ~name:"json" ([
    LPDoc {|Yojson bindings for Elpi: the plugin json (findlib package elpi-json)|};
    LPDoc {|license: GNU Lesser General Public License Version 2.1 or later|};
    LPDoc {|------------------------------------------------------------------------|};
  ] @ Elpi.API.PPX.to_list declaration @ [
    json_from_file;
    json_from_string;
    json_to_file;
    json_to_string;
    json_pretty_to_string;
  ])
