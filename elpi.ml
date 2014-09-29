open Lprun
open Lpdata

module F = Format

let type_err name exp got =
  F.eprintf "Wrong call to %s, %s expected, got %a\n%!"
    name exp (LP.prf_data []) got; exit 1

let protect f x = try f x with UnifFail _ -> raise NoClause

let check_list1 name t =
  match LP.look t with
  | LP.Seq (l,tl) when L.len l = 1 && LP.equal tl LP.mkNil -> L.hd l
  | _ -> type_err name "list of len 1" t

let check_list2 name t =
  match LP.look t with
  | LP.Seq (l,tl) when L.len l = 2 && LP.equal tl LP.mkNil -> L.hd l, L.get 1 l
  | _ -> type_err name "list of len 2" t

let check_list name t =
  match LP.look t with
  | LP.Seq (l,tl) when LP.equal tl LP.mkNil -> l
  | _ -> type_err name "list" t

let check_string name t =
  match LP.look t with
  | LP.Ext x when isString x -> getString x
  | _ -> type_err name "string" t

let extern_dd name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    let v1, v2 = check_list2 name t in
    protect (f v1 v2) s)
;;

let extern_sd name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    let k, v = check_list2 name t in
    let k = check_string name k in
    protect (f k v) s)
;;

let extern_s name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    let k = check_string name t in
    protect (f k) s)
;;

let extern_d name f =
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    protect (f t) s)
;;

let extern_l name f =      
  register_custom_predicate name (fun t s ->
    let t, s = Red.nf t s in
    match LP.look t with
    | LP.Seq(l,_) -> protect (f l) s
    | _ -> type_err name "list" t)
;;

module Extern = struct

let print t s =
  let unescape s =
    Str.global_replace (Str.regexp_string "\\n") "\n"
    (Str.global_replace (Str.regexp_string "\\t") "\t"
      s) in
  let t, s = Red.nf t s in
  match LP.look t with
  | LP.Ext t  when isString t -> F.eprintf "%s%!" (unescape (getString t)); s
  | _ -> F.eprintf "%a%!" (LP.prf_data []) t; s
;;
        
let printl l s = let s = L.fold print l s in F.eprintf "\n%!"; s

let abort =
  let aborts = ref 0 in
  fun text s ->
    incr aborts; if !aborts = int_of_string text then exit 1 else s
;;

let exit text s = exit (int_of_string text)

let trace_counter name value s =
  let n = Trace.get_cur_step name in
  protect (unify (LP.mkExt (mkString (string_of_int n))) value) s
;;

let incr, get, reset =
  let module M = Map.Make(struct type t = string let compare = compare end) in
  let counters = ref M.empty in
  let incr name s =
    try counters := M.add name (M.find name !counters + 1) !counters; s
    with Not_found -> counters := M.add name 1 !counters; s in
  let reset name s = counters := M.add name 0 !counters; s in
  let get name value s =
    let n = try M.find name !counters with Not_found -> 0 in
    protect (unify (LP.mkExt (mkString (string_of_int n))) value) s in
  incr, get, reset
;;

let parse text value s = protect (unify (LP.parse_data text) value) s
let read t s = unify (LP.mkExt (mkString (input_line stdin))) t s

let telescope ctx value s =
  let bind v t = LP.mapi LP.(fun i t ->
    if equal t v then mkDB i else t) 1 t in
  LP.(
    let ctx, s = Red.nf ctx s in
    let ctx = L.to_list (check_list "telescope" ctx) in
    if ctx = [] then unify mkNil value s else
    let t, binders = List.hd ctx, List.tl ctx in
    let binders = List.map (check_list2 "telescope") binders in
    let tele = List.fold_left (fun t (var,typ) ->
      fixApp (L.of_list [typ;mkBin 1 (bind var t)]))
      t binders in
    unify tele value s)
;;


end

open Extern

let register_std () =
  extern_s "abort" abort;
  extern_s "exit" exit;
  extern_d "print" print;
  extern_l "printl" printl;
  extern_sd "trace_counter" trace_counter;
  extern_s "incr" incr;
  extern_s "reset" reset;
  extern_sd "get" get;
  extern_sd "parse" parse;
  extern_d "read" read;
  extern_dd "telescope" telescope;
;;

