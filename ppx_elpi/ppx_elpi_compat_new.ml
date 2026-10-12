open Ppxlib

(* ppxlib >= 0.36: [fun a b -> e] is a single Pexp_function node *)
let fun_params e =
  let rec params acc e =
    match e.pexp_desc with
    | Pexp_function (ps, None, Pfunction_body body)
      when List.for_all (function
        | { pparam_desc = Pparam_val (Nolabel, None, { ppat_desc = Ppat_var _; _ }); _ } -> true
        | _ -> false) ps ->
        let names = List.map (function
          | { pparam_desc = Pparam_val (_, _, { ppat_desc = Ppat_var { txt; _ }; _ }); _ } -> txt
          | _ -> assert false) ps in
        params (List.rev_append names acc) body
    | _ -> List.rev acc, e in
  params [] e
