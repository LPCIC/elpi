(* provides:
        
    let rec f x =
     [%trace "f" (fun fmt -> .. x ..) begin
         match x with
         | K1 -> ...
         | K2 x -> [%tcall f x]
         | K2(x,y) ->
            let z = f x in
            [%spy "z" (fun fmt -> .. z ..) z];
            [%spyif "z" b (fun fmt -> .. z ..) z];
            [%log "K2" "whatever" 37];
            z + f y
     end]
     
  All syntactic extensions vanish if --off is passed
  to the ppx rewriter
     
  requires:
*)
open Migrate_parsetree.Ast_404
open Ppx_tools_404

open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

let trace name ppfun body = [%expr
  let wall_clock = Unix.gettimeofday () in
  Trace.Runtime.enter [%e name] [%e ppfun];
  try
    let rc = [%e body] in
    let elapsed = Unix.gettimeofday () -. wall_clock in
    Trace.Runtime.exit [%e name] false elapsed;
    rc
  with
  | Trace.Runtime.TREC_CALL(f,x) ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace.Runtime.exit [%e name] true elapsed;
      Obj.obj f (Obj.obj x)
  | e ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace.Runtime.exit [%e name] false elapsed;
      raise e
]

let spy name pp data =
  [%expr Trace.Runtime.print [%e name] [%e pp] [%e data]]

let spyif name cond pp data =
  [%expr if [%e cond] then Trace.Runtime.print [%e name] [%e pp] [%e data]]

let log name key data =
  [%expr Trace.Runtime.log [%e name] [%e key] [%e data]]

let cur_pred name =
  [%expr Trace.Runtime.cur_pred [%e name]]

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
  [%expr raise (Trace.Runtime.TREC_CALL ([%e papp], Obj.repr [%e last]))]

let enabled = ref false

let args = [
   "--trace_ppx-on",Arg.Set enabled,"Enable trace_ppx" ;
   "--trace_ppx-off",Arg.Clear enabled,"Disable trace_ppx" ;
  ]
let reset_args () =
  enabled := false

let err ~loc str =
  raise (Location.Error(Location.error ~loc str))

let trace_mapper config cookies =
  { default_mapper with expr = fun mapper expr ->
  let aux = mapper.expr mapper in
  match expr with
  | { pexp_desc = Pexp_extension ({ txt = "trace"; loc }, pstr) } ->
      let err () = err ~loc "use: [%trace id ?pred pp code]" in
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,pp);(_,code)]) },_)} ] ->
        let pp =
          match pp with
          | { pexp_desc = Pexp_apply(hd,args) } ->
             [%expr fun fmt -> [%e mkapp [%expr Format.fprintf fmt]
                (hd :: List.map snd args)]]
          | _ -> pp in
        if !enabled then trace (aux name) (aux pp) (aux code)
        else aux code
      | _ -> err ()
      end
  | { pexp_desc = Pexp_extension ({ txt = "tcall"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(hd,args) } as e,_)} ] ->
        if !enabled then tcall (aux hd) (List.map (fun (_,e) -> aux e) args)
        else aux e
      | _ -> err ~loc "use: [%tcall f args]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "spy"; loc }, pstr) } ->
      let err () = err ~loc "use: [%spy id ?pred pp data]" in
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,pp);(_,code)]) },_)} ] ->
        if !enabled then spy (aux name) (aux pp) (aux code)
        else [%expr ()]
      | _ -> err ()
      end
  | { pexp_desc = Pexp_extension ({ txt = "spyif"; loc }, pstr) } ->
      let err () = err ~loc "use: [%spyif id ?pred cond pp data]" in
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,cond);(_,pp);(_,code)]) },_)} ] ->
        if !enabled then spyif (aux name) (aux cond) (aux pp) (aux code)
        else [%expr ()]
      | _ -> err ()
      end
  | { pexp_desc = Pexp_extension ({ txt = "log"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,key);(_,code)]) },_)} ] ->
        if !enabled then log (aux name) (aux key) (aux code)
        else [%expr ()]
      | _ -> err ~loc "use: [%log id data]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "cur_pred"; loc }, pstr) } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(name, _)} ] ->
        if !enabled then cur_pred (aux name)
        else [%expr ()]
      | _ -> err ~loc "use: [%cur_pred id]"
      end
  | x -> default_mapper.expr mapper x;
}

open Migrate_parsetree
let () =
  Driver.register ~name:"trace" ~args ~reset_args
    Versions.ocaml_404 trace_mapper
;;

