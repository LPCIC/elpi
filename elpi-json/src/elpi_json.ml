(* elpi-json: Yojson bindings for Elpi, the plugin of package elpi-json
   (accumulate "+elpi-json"). Taken from rocq-elpi's apps/json, without its
   Rocq specific code. *)
open Elpi.API

let pairC = ContextualConversion.(!>>>) Elpi.Builtin.pair
let stringC = ContextualConversion.(!>) BuiltInData.string

let json : Yojson.Basic.t Conversion.t = AlgebraicData.(declare {
  ty = Conversion.TyName "json";
  doc = "Yojson.Basic.t";
  pp = Yojson.Basic.pp;
  constructors = [
    K("json.null","",N,B `Null,M (fun ~ok ~ko -> function `Null -> ok | _ -> ko ()));
    K("json.bool","",A(Elpi.Builtin.bool,N),B (fun x -> `Bool x),M (fun ~ok ~ko -> function `Bool x -> ok x | _ -> ko ()));
    K("json.int","",A(BuiltInData.int,N),B (fun x -> `Int x),M (fun ~ok ~ko -> function `Int x -> ok x | _ -> ko ()));
    K("json.float","",A(BuiltInData.float,N),B (fun x -> `Float x),M (fun ~ok ~ko -> function `Float x -> ok x | _ -> ko ()));
    K("json.string","",A(BuiltInData.string,N),B (fun x -> `String x),M (fun ~ok ~ko -> function `String x -> ok x | _ -> ko ()));
    K("json.assoc","key value pairs. When generated from built-in predicates, keys are sorted",
      C((fun x -> BuiltInData.listC (pairC stringC x)),N),
      B (fun x -> `Assoc x),
      M (fun ~ok ~ko -> function
        | `Assoc x -> ok (List.stable_sort (fun (x,_) (y,_) -> String.compare x y) x)
        | _ -> ko ()));
    K("json.list","",C(BuiltInData.listC,N),B (fun x -> `List x),M (fun ~ok ~ko -> function `List x -> ok x | _ -> ko ()));
  ];
}) |> ContextualConversion.(!<)

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
    try !: (Yojson.Basic.from_file ~fname:f f) +! mkOK
    with Yojson.Json_error s | Sys_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_from_string = MLCode(Pred("json.from_string",
  In(string,"String",
  Out(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.from_string reads J from String.
If D is error then J is not assigned.|}))),
  (fun s _ _ ~depth:_ ->
    try !: (Yojson.Basic.from_string s) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_to_file = MLCode(Pred("json.to_file",
  In(string,"File",
  In(json,"J",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_file writes J to File.|}))),
  (fun f j _ ~depth:_ ->
    try Yojson.Basic.to_file f j; !: mkOK
    with Yojson.Json_error s | Sys_error s -> !: (mkERROR s))),
  DocAbove)

let json_to_string = MLCode(Pred("json.to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.to_string writes J to a compact string S.|}))),
  (fun j _ _ ~depth:_ ->
    try !: (Yojson.Basic.to_string ~std:true j) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let json_pretty_to_string = MLCode(Pred("json.pretty_to_string",
  In(json,"J",
  Out(string,"S",
  Out(diagnostic,"D",
  Easy {|like Yojson.Basic.pretty_to_string writes J to a nice string S.|}))),
  (fun j _ _ ~depth:_ ->
    try !: (Yojson.Basic.pretty_to_string ~std:true j) +! mkOK
    with Yojson.Json_error s -> ?: None +! (mkERROR s))),
  DocAbove)

let builtins : Setup.builtins = Plugin.register ~name:"elpi-json" [
    LPDoc {|Yojson bindings for Elpi, the plugin of package elpi-json|};
    LPDoc {|license: GNU Lesser General Public License Version 2.1 or later|};
    LPDoc {|------------------------------------------------------------------------|};
    MLData json;
    json_from_file;
    json_from_string;
    json_to_file;
    json_to_string;
    json_pretty_to_string;
  ]
