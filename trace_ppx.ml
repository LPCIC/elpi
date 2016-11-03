(* provides:
        
    let rec f x =
     [%trace "f" (fun fmt -> .. x ..) begin
         match x with
         | K1 -> ...
         | K2 x -> [%tcall f x]
         | K2(x,y) ->
            let z = f x in
            [%spy "z" (fun fmt -> .. z ..) z];
            z + f y
     end]

  If env variable TRACE is undefined, no code is added.

  requires:
*)

open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

let trace name ppfun body = [%expr
  let wall_clock = Unix.gettimeofday () in
  Elpi_trace.enter [%e name] [%e ppfun];
  try
    let rc = [%e body] in
    let elapsed = Unix.gettimeofday () -. wall_clock in
    Elpi_trace.exit [%e name] false elapsed;
    rc
  with
  | Elpi_trace.TREC_CALL(f,x) ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Elpi_trace.exit [%e name] true elapsed;
      Obj.obj f (Obj.obj x)
  | e ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Elpi_trace.exit [%e name] false elapsed;
      raise e
]

let spy name pp data =
  [%expr Elpi_trace.print [%e name] [%e pp] [%e data]]

let log name key data =
  [%expr Elpi_trace.log [%e name] [%e key] [%e data]]

let rec mkapp f = function
  | [] -> f
  | x :: xs -> mkapp [%expr [%e f] [%e x]] xs

let tcall hd args =
  let l = List.rev (hd :: args) in
  let last, rest = List.hd l, List.tl l in
  let papp =
    match List.rev rest with
    | [] -> assert false
    | f::a -> [%expr Obj.repr [%e mkapp f a]] in
  [%expr raise (Elpi_trace.TREC_CALL ([%e papp], Obj.repr [%e last]))]

let enabled =
  try ignore(Sys.getenv "TRACE"); true
  with Not_found -> false

let err ~loc str =
  raise (Location.Error(Location.error ~loc str))

let trace_mapper argv = { default_mapper with expr = fun mapper expr ->
  let aux = mapper.expr mapper in
  match expr with
  | { pexp_desc = Pexp_extension ({ txt = "trace"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,pp);(_,code)]) },_)} ] ->
        let pp =
          match pp with
          | { pexp_desc = Pexp_apply(hd,args) } ->
             [%expr fun fmt -> [%e mkapp [%expr Format.fprintf fmt]
                (hd :: List.map snd args)]]
          | _ -> pp in
        if enabled then trace (aux name) (aux pp) (aux code)
        else aux code
      | _ -> err ~loc "use: [%trace id pp code]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "tcall"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(hd,args) } as e,_)} ] ->
        if enabled then tcall (aux hd) (List.map (fun (_,e) -> aux e) args)
        else aux e
      | _ -> err ~loc "use: [%tcall f args]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "spy"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,pp);(_,code)]) },_)} ] ->
        if enabled then spy (aux name) (aux pp) (aux code)
        else [%expr ()]
      | _ -> err ~loc "use: [%spy id pp data]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "log"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,key);(_,code)]) },_)} ] ->
        if enabled then log (aux name) (aux key) (aux code)
        else [%expr ()]
      | _ -> err ~loc "use: [%log id data]"
      end
  | x -> default_mapper.expr mapper x;
}

let () = register "trace" trace_mapper

