(**
    elpi.trace.ppx provides the following syntax extensions:

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

  If
    --cookie "elpi_trace=\"true\""
  is not passed to the ppx rewriter:

    - [%trace "foo" pp code] ---> code
    - [%tcall f x] ---> f x
    - [%spy ...] [%spyl ...] and [%log ...] ---> ()
    - f x (y[@trace]) z ---> f x z
    - let x[@trace] = .. in e ---> e
    - type x = { a : T; b : T [@trace] } ---> type x = { a : T }
    - { a; b = b [@trace] } ---> { a } (in both patterns and expressions)
    - T -> (S[@trace]) -> U  --->  T -> U

  In records, the shorcut "x" to mean "x = x" does not work, you have to use the
  longer form.

*)

open Ppxlib
open Ast_builder.Default

let err ~loc str =
  Location.raise_errorf~loc "%s" str

let trace ~loc name ppfun body = [%expr
  let wall_clock = Unix.gettimeofday () in
  Trace_ppx_runtime.Runtime.enter [%e name] [%e ppfun];
  try
    let rc = [%e body] in
    let elapsed = Unix.gettimeofday () -. wall_clock in
    Trace_ppx_runtime.Runtime.exit [%e name] false None elapsed;
    rc
  with
  | Trace_ppx_runtime.Runtime.TREC_CALL(f,x) ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace_ppx_runtime.Runtime.exit [%e name] true None elapsed;
      Obj.obj f (Obj.obj x)
  | e ->
      let elapsed = Unix.gettimeofday () -. wall_clock in
      Trace_ppx_runtime.Runtime.exit [%e name] false (Some e) elapsed;
      raise e
]

let spy ~loc err ?(cond=[%expr true]) ?gid name pp =
  let ppl =
    let rec aux = function
      | [] -> [%expr []]
      | [_] -> err ~loc ()
      | p :: x :: xs -> [%expr Trace_ppx_runtime.Runtime.J([%e p],[%e x]) :: [%e aux xs]]
      in
    aux pp in
  match gid with
  | None -> [%expr if [%e cond] then Trace_ppx_runtime.Runtime.info [%e name] [%e ppl]]
  | Some gid -> [%expr if [%e cond] then Trace_ppx_runtime.Runtime.info ~goal_id:(Util.UUID.hash [%e gid]) [%e name] [%e ppl]]

let spyl ~loc err ?(cond=[%expr true]) ?gid name pp =
  let ppl =
    let rec aux = function
      | [] -> [%expr []]
      | [_] -> err ~loc ()
      | p :: xl :: xs -> [%expr List.map (fun x -> Trace_ppx_runtime.Runtime.J([%e p],x)) [%e xl] @ [%e aux xs]]
      in
    aux pp in
  match gid with
  | None -> [%expr if [%e cond] then Trace_ppx_runtime.Runtime.info [%e name] [%e ppl]]
  | Some gid -> [%expr if [%e cond] then Trace_ppx_runtime.Runtime.info ~goal_id:(Util.UUID.hash [%e gid]) [%e name] [%e ppl]]

let log ~loc name key data =
  [%expr Trace_ppx_runtime.Runtime.log [%e name] [%e key] [%e data]]

let cur_pred ~loc name =
  [%expr Trace_ppx_runtime.Runtime.set_cur_pred [%e name]]

let tcall ~loc hd args =
  let l = List.rev (hd :: args) in
  let last, rest = List.hd l, List.tl l in
  let papp =
    match List.rev rest with
    | [] -> assert false
    | f::a -> [%expr Obj.repr [%e eapply ~loc f a]] in
  [%expr raise (Trace_ppx_runtime.Runtime.TREC_CALL ([%e papp], Obj.repr [%e last]))]

let template_db : (string * expression) list ref = ref []

let template ~loc name args =
  if not (List.mem_assoc name !template_db) then
    Location.raise_errorf ~loc "template %s not found" name;
  let e = List.assoc name !template_db in
  let rec aux e = function
    | [] -> e
    | arg :: args ->
       match e with
       | [%expr fun [%p? name ] -> [%e? v] ] ->
           [%expr let [%p name ] = [%e arg ] in [%e aux v args ]]
       | _ -> Location.raise_errorf ~loc "template %s:  too many arguments" name
  in
    aux e args

let enabled = ref false

let has_iftrace_attribute (l : attributes) =
  List.exists (fun {attr_name = { txt; _ } ; _ } -> txt = "trace") l

let has_iftrace { ptyp_attributes = l; _ } = has_iftrace_attribute l

let att_elpi_template =
  let open Ppxlib.Ast_pattern in
  Attribute.(declare "elpi.template" Context.value_binding (pstr nil) ())

let map_template = object
  inherit Ast_traverse.map as super

  method! structure_item i =
    let i = super#structure_item i in
    match i.pstr_desc with
    | Pstr_value(Nonrecursive, [ { pvb_pat = { ppat_desc = Ppat_var { txt; _ } ; _ }; _ } as vb]) ->
       begin match Attribute.get att_elpi_template vb with
       | Some () ->
            template_db := (txt, vb.pvb_expr) :: !template_db;
            let loc = i.pstr_loc in [%stri let () = ()]
       | None -> i
      end
    | _ -> i

end

let map_trace = object(self)
  inherit Ast_traverse.map as super

  method! core_type ty =
    let ty = super#core_type ty  in
    match ty.ptyp_desc with
    | Ptyp_arrow(lbl,src,tgt) when not !enabled ->
      if has_iftrace src then tgt
      else { ty with ptyp_desc = Ptyp_arrow(lbl,self#core_type src, self#core_type tgt) }
   | Ptyp_tuple l when not !enabled ->
      let l = l |> List.filter (fun x -> not(has_iftrace x)) in
      let l = List.map self#core_type l in
      { ty with ptyp_desc = Ptyp_tuple l }
   | _ -> ty

  method! pattern p =
    let p = super#pattern p  in
    match p.ppat_desc with
    | Ppat_record(lp,c) when not !enabled ->
        let lp = lp |> List.filter (fun (_,{ ppat_attributes = l; _ }) ->
          not (has_iftrace_attribute l)) in
        let lp = List.map (fun (x,y) -> x, self#pattern y) lp in
        { p with ppat_desc = Ppat_record(lp,c) }
    | Ppat_tuple lp when not !enabled ->
        let lp = lp |> List.filter (fun { ppat_attributes = l; _ } ->
          not (has_iftrace_attribute l)) in
        let lp = List.map self#pattern lp in
        { p with ppat_desc = Ppat_tuple lp }
    | _ -> p

  method! type_declaration tyd =
    let tyd = super#type_declaration tyd in
    match tyd.ptype_kind with
    | Ptype_record lbls when not !enabled ->
        let lbls = lbls |> List.filter (fun { pld_attributes = l; _ } ->
          not (has_iftrace_attribute l)) in
        { tyd with ptype_kind = Ptype_record lbls }
    | _ -> tyd

  method! expression e =
    let e = super#expression e in
    match e.pexp_desc with
    | Pexp_record (fields,def) when not !enabled ->
        let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
        let fields = fields |> List.filter (fun (_,e) -> not (has_iftrace e)) in
        let fields = List.map (fun (x,y) -> x, self#expression y) fields in
        let def = match def with None -> None | Some e -> Some (self#expression e) in
        { e with pexp_desc = Pexp_record (fields,def)}
    | Pexp_apply (hd,args) when not !enabled ->
        let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
        let args = args |> List.filter (fun (_,e) -> not (has_iftrace e)) in
        let args = List.map (fun (x,y) -> x, self#expression y) args in
        { e with pexp_desc = Pexp_apply (hd,args)}
    | Pexp_fun(_,_,pat,rest) when not !enabled ->
        let has_iftrace { ppat_attributes = l; _ } = has_iftrace_attribute l in
        if has_iftrace pat then self#expression rest
        else e
    | Pexp_let(_,[{pvb_pat = { ppat_attributes = l; _}; _}],rest) when not !enabled ->
        if has_iftrace_attribute l then self#expression rest
        else e
    | Pexp_tuple l when not !enabled ->
        let has_iftrace { pexp_attributes = l; _ } = has_iftrace_attribute l in
        let l = l |> List.filter (fun e -> not (has_iftrace e)) in
        let l = List.map self#expression l in
        { e with pexp_desc = Pexp_tuple l }
    | _ -> e

end

(* ----------------------------------------------------------------- *)
(* ------------------------ %extension ----------------------------- *)
(* ----------------------------------------------------------------- *)


let is_string_literal = function
  | { pexp_desc = Pexp_constant (Pconst_string _); _ } -> true
  | _ -> false

let is_gid lbl = lbl = Labelled "gid"
let is_cond lbl = lbl = Labelled "cond"
let pull f l =
  let rec pull acc = function
    | [] -> None, l
    | (x,y) :: xs when f x -> Some y, List.rev acc @ xs
    | x :: xs -> pull (x :: acc) xs in
  pull [] l

let err_spy ~loc () = err ~loc "use: [%spy id pp x] or [%spy id ~gid ~cond pp x]"

let spyl_expand_function ~loc ~path:_ = function
  | { pexp_desc = Pexp_apply(name, args); _ } when is_string_literal name ->
        let cond, args = pull is_cond args in
        let gid, args = pull is_gid args in
        if !enabled then spyl ~loc err_spy ?cond ?gid name (List.map snd args)
        else [%expr ()]
  | _ -> err_spy ~loc ()

let spyl_extension =
  Extension.declare
    "spyl"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    spyl_expand_function

let spyl_rule = Context_free.Rule.extension spyl_extension

let spy_expand_function ~loc ~path:_ = function
  | name when is_string_literal name ->
        if !enabled then spy ~loc err_spy name []
        else [%expr ()]
  | { pexp_desc = Pexp_apply(name, args); _ } when is_string_literal name ->
        let cond, args = pull is_cond args in
        let gid, args = pull is_gid args in
        if !enabled then spy ~loc err_spy ?cond ?gid name (List.map snd args)
        else [%expr ()]
  | _ -> err_spy ~loc ()

let spy_extension =
  Extension.declare
    "spy"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    spy_expand_function

let spy_rule = Context_free.Rule.extension spy_extension

(* ----------------------------------------------------------------- *)

let tcall_expand_function ~loc ~path:_ = function
  | { pexp_desc = Pexp_apply (hd,args); _ } when !enabled ->
       tcall ~loc hd (List.map snd args)
  | { pexp_desc = Pexp_apply(hd,args); _ } as r ->
       let hd = [%expr ([%e hd][@tailcall]) ] in
       { r with pexp_desc = Pexp_apply(hd,args) }
  | _ -> err ~loc "use: [%tcall f args]"

let tcall_extension =
  Extension.declare
    "tcall"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    tcall_expand_function

let tcall_rule = Context_free.Rule.extension tcall_extension

(* ----------------------------------------------------------------- *)

let trace_expand_function ~loc ~path:_ = function
   |  [%expr ([%e? name] [%e? code]) ] ->
        if !enabled then trace ~loc name [%expr fun _ -> ()] code
        else code
   |  [%expr ([%e? name] [%e? pp] [%e? code]) ] ->
        let pp =
          match pp with
          | { pexp_desc = Pexp_apply(hd,args); _ } ->
              [%expr fun fmt -> [%e eapply ~loc [%expr Format.fprintf fmt] (hd :: List.map snd args)]]
          | x -> x in
        if !enabled then trace ~loc name pp code
        else code
   | _ -> err ~loc "use: [%trace name pp code]"

let trace_extension =
  Extension.declare
    "trace"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    trace_expand_function

let trace_rule = Context_free.Rule.extension trace_extension

(* ----------------------------------------------------------------- *)

let cur_pred_expand_function ~loc ~path:_ name =
  if !enabled then cur_pred ~loc name
  else [%expr ()]

let cur_pred_extension =
  Extension.declare
    "cur_pred"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    cur_pred_expand_function

let cur_pred_rule = Context_free.Rule.extension cur_pred_extension

(* ----------------------------------------------------------------- *)

let log_expand_function ~loc ~path:_ = function
  | [%expr ([%e? name] [%e? key] [%e? code]) ] ->
        if !enabled then log ~loc name key code
        else [%expr ()]
  | _ -> err ~loc "use: [%log id data]"

let log_extension =
  Extension.declare
    "log"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    log_expand_function

let log_rule = Context_free.Rule.extension log_extension

(* ----------------------------------------------------------------- *)

let template_expand_function ~loc ~path:_ e = match e.pexp_desc with
  | Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident name; _}; _ }, args) ->
        template ~loc name (List.map snd args)
  | _ -> err ~loc "use: [%elpi.template id data..]"

let template_extension =
  Extension.declare
    "elpi.template"
    Extension.Context.expression
    Ast_pattern.(single_expr_payload __)
    template_expand_function

let template_rule = Context_free.Rule.extension template_extension


(* ----------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)
(* ----------------------------------------------------------------- *)

let arg_trace t =
  match Driver.Cookies.get t "elpi_trace" Ast_pattern.(estring __) with
  | Some "true" -> enabled := true
  | _ -> enabled := false

let () =
  Driver.Cookies.add_handler arg_trace;
  Driver.register_transformation
    ~preprocess_impl:map_template#structure
    ~rules:[ log_rule; cur_pred_rule; trace_rule; tcall_rule; spy_rule; spyl_rule; template_rule ]
    ~impl:map_trace#structure
    ~intf:map_trace#signature
    "elpi.trace"