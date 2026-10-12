open Ppxlib

(* ppxlib < 0.36: [fun a b -> e] is nested Pexp_fun nodes *)
let fun_params e =
  let rec params acc e =
    match e.pexp_desc with
    | Pexp_fun (Nolabel, None, { ppat_desc = Ppat_var { txt; _ }; _ }, body) ->
        params (txt :: acc) body
    | _ -> List.rev acc, e in
  params [] e
