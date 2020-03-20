(* provides:

    type t = { a : T; b : S [@trace] }

    let rec f x (w[@trace]) =
     [%trace "f" (fun fmt -> .. x ..) begin
         match x with
         | K1 -> ...
         | K2 x -> [%tcall f x]
         | K2(x,y) ->
            let z = f x in
            [%spy "z" ~gid ~cond (fun fmt z -> .. z ..) z];
            [%spyl "z" ~gid ~cond (fun fmt z -> .. z ..) zs];
            [%log "K2" "whatever" 37];
            let x[@trace] = ... in e
            let w = { a; b = b[@trace ] } in
            match w with
            | { a; b = b [@trace] } ->
               z + f y (b[@trace])
     end]

  If --off is passed to the ppx rewriter:
    - [%trace "foo" pp code] ---> code
    - [%tcall f x] ---> f x
    - [%spy ...] [%spyl ...] and [%log ...] ---> ()
    - f x (y[@trace]) z ---> f x z
    - type x = { a : T; b : T [@trace] } ---> type x = { a : T }
    - { a; b = b [@trace] } ---> { a } (in both patterns and expressions)
    - T -> (S[@trace]) -> U  --->  T -> U
  The shorcut "x" to mean "x = x" does not work, you have to use the longer form

  requires:
*)
module Ast_404 = Migrate_parsetree.Ast_404
open Ast_404

open Ast_mapper
open Asttypes
open Parsetree

let trace name ppfun body = [%expr
  let wall_clock = Unix.gettimeofday () in
  Trace.Runtime.enter [%e name] [%e ppfun];
  try
    let rc = [%e body] in
    let elapsed = Unix.gettimeofday () -. wall_clock in
    Trace.Runtime.exit [%e name] false None elapsed;
    rc
  with
  | Trace.Runtime.TREC_CALL(f,x) ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace.Runtime.exit [%e name] true None elapsed;
      Obj.obj f (Obj.obj x)
  | e ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace.Runtime.exit [%e name] false (Some e) elapsed;
      raise e
]

let err ~loc str =
  raise (Location.Error(Location.error ~loc str))

let spy err ?(cond=[%expr true]) ?gid name pp =
  let ppl =
    let rec aux = function
      | [] -> [%expr []]
      | [_] -> err ()
      | p :: x :: xs -> [%expr Trace.Runtime.J([%e p],[%e x]) :: [%e aux xs]]
      in
    aux pp in
  match gid with
  | None -> [%expr if [%e cond] then Trace.Runtime.info [%e name] [%e ppl]]
  | Some gid -> [%expr if [%e cond] then Trace.Runtime.info ~goal_id:(Util.UUID.hash [%e gid]) [%e name] [%e ppl]]

let spyl err ?(cond=[%expr true]) ?gid name pp =
  let ppl =
    let rec aux = function
      | [] -> [%expr []]
      | [_] -> err ()
      | p :: xl :: xs -> [%expr List.map (fun x -> Trace.Runtime.J([%e p],x)) [%e xl] @ [%e aux xs]]
      in
    aux pp in
  match gid with
  | None -> [%expr if [%e cond] then Trace.Runtime.info [%e name] [%e ppl]]
  | Some gid -> [%expr if [%e cond] then Trace.Runtime.info ~goal_id:(Util.UUID.hash [%e gid]) [%e name] [%e ppl]]

let log name key data =
  [%expr Trace.Runtime.log [%e name] [%e key] [%e data]]

let cur_pred name =
  [%expr Trace.Runtime.set_cur_pred [%e name]]

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

let has_iftrace_attribute (l : attributes) =
  List.exists (fun ( { txt; _ },_) -> txt = "trace") l

let trace_mapper _config _cookies =
  { default_mapper with

expr = begin fun mapper expr ->
  let aux = mapper.expr mapper in
  match expr with
  | { pexp_desc = Pexp_extension ({ txt = "trace"; loc; _ }, pstr); _ } ->
      let err () = err ~loc "use: [%trace pp code]" in
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,args); _ },_); _} ] ->
        let pp, code =
          match args with
          | [_,code] -> [%expr fun _ -> ()], code
          | [(_,pp);(_,code)] ->
              begin match pp with
              | { pexp_desc = Pexp_apply(hd,args); _ } ->
                 [%expr fun fmt -> [%e mkapp [%expr Format.fprintf fmt]
                    (hd :: List.map snd args)]], code
              | _ -> pp, code
              end
          | _ -> err () in
        if !enabled then trace (aux name) (aux pp) (aux code)
        else aux code
      | _ -> err ()
      end
  | { pexp_desc = Pexp_extension ({ txt = "tcall"; loc }, pstr); _ } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply _; _ } as e,_); _} ] ->
        begin match aux e with
        | { pexp_desc = Pexp_apply(hd,args); _ } when !enabled ->
           tcall hd (List.map snd args)
        | { pexp_desc = Pexp_apply(hd,args); _ } as r ->
           { r with pexp_desc = Pexp_apply(
               ({ hd with pexp_attributes = (({ txt = "tailcall"; loc },PStr []) :: hd.pexp_attributes) }),
                 args) }
        | x -> x
        end
      | _ -> err ~loc "use: [%tcall f args]"
      end
  | { pexp_desc = Pexp_extension ({ txt; loc; _ }, pstr); _ } when txt = "spy" || txt = "spyl" ->
      let err () = err ~loc "use: [%spy id pp x] or [%spy id ~gid ~cond pp x]" in
      let is_string_literal = function
        | { pexp_desc = Pexp_constant (Pconst_string _); _ } -> true
        | _ -> false in
       let is_gid lbl = lbl = Labelled "gid" in
       let is_cond lbl = lbl = Labelled "cond" in
       let pull f l =
         let rec pull acc = function
           | [] -> None, l
           | (x,y) :: xs when f x -> Some y, List.rev acc @ xs
           | x :: xs -> pull (x :: acc) xs in
          pull [] l in
      let expr_of_msg (_,msg) = aux msg in
      begin match pstr with
      | PStr [{ pstr_desc = Pstr_eval(name,_); _ }] when is_string_literal name ->
        if !enabled then spy err name []
        else [%expr ()]
      | PStr [{ pstr_desc = Pstr_eval(
               { pexp_desc = Pexp_apply(name, args); _ },_); _} ] when is_string_literal name ->
        let cond, args = pull is_cond args in
        let gid, args = pull is_gid args in
        if !enabled then
          if txt = "spy" then spy err ?cond ?gid name (List.map expr_of_msg args)
          else if txt = "spyl" then spyl err ?cond ?gid name (List.map expr_of_msg args)
          else assert false
        else [%expr ()]
      | _ -> err ()
      end
  | { pexp_desc = Pexp_extension ({ txt = "log"; loc; _ }, pstr); _ } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(
              { pexp_desc = Pexp_apply(name,[(_,key);(_,code)]); _ },_); _} ] ->
        if !enabled then log (aux name) (aux key) (aux code)
        else [%expr ()]
      | _ -> err ~loc "use: [%log id data]"
      end
  | { pexp_desc = Pexp_extension ({ txt = "cur_pred"; loc; _ }, pstr); _ } ->
      begin match pstr with
      | PStr [ { pstr_desc = Pstr_eval(name, _); _} ] ->
        if !enabled then cur_pred (aux name)
        else [%expr ()]
      | _ -> err ~loc "use: [%cur_pred id]"
      end
  | { pexp_desc = Pexp_record (fields,def); _ } as r when not !enabled ->
      let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
      let fields = fields |> List.filter (fun (_,e) -> not (has_iftrace e)) in
      let r = { r with pexp_desc = Pexp_record (fields,def)} in
      default_mapper.expr mapper r
  | { pexp_desc = Pexp_apply (hd,args); _ } as r when not !enabled ->
      let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
      let args = args |> List.filter (fun (_,e) -> not (has_iftrace e)) in
      let r = { r with pexp_desc = Pexp_apply (hd,args)} in
      default_mapper.expr mapper r
  | { pexp_desc = Pexp_fun(_,_,pat,rest); _ } as r when not !enabled ->
      let has_iftrace { ppat_attributes = l; _ } = has_iftrace_attribute l in
      if has_iftrace pat then aux rest
      else default_mapper.expr mapper r
  | { pexp_desc = Pexp_let(_,[{pvb_pat = { ppat_attributes = l; _}; _}],rest); _ } as r when not !enabled ->
      if has_iftrace_attribute l then aux rest
      else default_mapper.expr mapper r
  | { pexp_desc = Pexp_tuple l; _ } as r when not !enabled ->
      let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
      let l = l |> List.filter (fun e -> not (has_iftrace e)) in
      let r = { r with pexp_desc = Pexp_tuple l } in
      default_mapper.expr mapper r
  | x -> default_mapper.expr mapper x;
end;

type_declaration = begin fun mapper type_declaration ->
  let type_declaration = match type_declaration with
  | { ptype_kind = Ptype_record lbls; _ } as r when not !enabled ->
     let lbls = lbls |> List.filter (fun { pld_attributes = l; _ } ->
       not (has_iftrace_attribute l)) in
     { r with ptype_kind = Ptype_record lbls }
  | x -> x in
  default_mapper.type_declaration mapper type_declaration
end;

pat = begin fun mapper pat ->
  let pat = default_mapper.pat mapper pat in
  match pat with
  | { ppat_desc = Ppat_record(lp,c); _ } as r when not !enabled ->
      let lp = lp |> List.filter (fun (_,{ ppat_attributes = l; _ }) ->
        not (has_iftrace_attribute l)) in
      { r with ppat_desc = Ppat_record(lp,c) }
  | { ppat_desc = Ppat_tuple lp; _ } as r when not !enabled ->
      let lp = lp |> List.filter (fun { ppat_attributes = l; _ } ->
        not (has_iftrace_attribute l)) in
      { r with ppat_desc = Ppat_tuple lp }
  | x -> x
end;

typ = begin fun mapper ty ->
  let ty = default_mapper.typ mapper ty in
  let aux = mapper.typ mapper in
  match ty with
  | { ptyp_desc = Ptyp_arrow(lbl,src,tgt); _ } as r when not !enabled ->
    let has_iftrace { ptyp_attributes = l; _ } = has_iftrace_attribute l in
    if has_iftrace src then
      aux tgt
    else
      { r with ptyp_desc = Ptyp_arrow(lbl,aux src, aux tgt) }
  | { ptyp_desc = Ptyp_tuple l; _ } as r when not !enabled ->
    let has_iftrace { ptyp_attributes = l; _ } = has_iftrace_attribute l in
    let l = l |> List.filter (fun x -> not(has_iftrace x)) in
    { r with ptyp_desc = Ptyp_tuple l }
  | x -> x
end;

}

open Migrate_parsetree
let () =
  Driver.register ~name:"trace" ~args ~reset_args
    Versions.ocaml_404 trace_mapper
;;

