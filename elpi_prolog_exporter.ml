(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module F = Elpi_ast.Func
module Fmt = Format

open Elpi_ast
open Elpi_runtime
open Elpi_util
open Constants

(* pp for first-order prolog *) 
let xppterm_prolog ~nice names f t =
  let pp_app f pphd pparg (hd,args) =
   if args = [] then pphd f hd
   else begin
    Fmt.fprintf f "@[<hov 1>%a(%a@]" pphd hd (pplist pparg ",") args;
    Fmt.fprintf f "%s" ")";
   end in
  let ppconstant f c = Fmt.fprintf f "%s" (show c) in
  let rec pp_arg f n =
   let name= try List.nth names n with Failure _ -> "A" ^ string_of_int n in
   Fmt.fprintf f "%s" name
  and aux f = function
      App (hd,x,xs) ->
        if hd==eqc then
         Fmt.fprintf f "@[<hov 1>%a@ =@ %a@]" aux x aux (List.hd xs) 
        else if hd==orc then        
                       (* (%a) ? *)
         Fmt.fprintf f "%a" (pplist aux ";") (x::xs)  
        else if hd==andc || hd == andc2 then    
         Fmt.fprintf f "%a" (pplist aux ",") (x::xs)  
        else if hd==rimplc then (
          assert (List.length xs = 1);
          Fmt.fprintf f "@[<hov 1>(%a@ :-@ %a@])" aux x aux (List.hd xs)
        ) else pp_app f ppconstant aux (hd,x::xs) 
    | Cons _ | Nil -> assert false (* TODO *)
    | Custom (hd,xs) ->  assert false;
    | UVar _
    | AppUVar _ -> assert false
    | Arg (n,0) -> pp_arg f n
    | Arg _
    | AppArg(_,_) -> assert false
    | Const s -> ppconstant f s
    | Lam t -> assert false;
    | CData x -> CData.pp f x
  in
    aux f t
;;

let prologppterm = xppterm_prolog ~nice:true

(*let pp_FOprolog p = assert false (*CSC: port the code, see function above List.iter (fun { Elpi_parser.head = a; hyps = f } ->
  let amap, cmap = empty_amap, ConstMap.empty in
let amap, a = stack_term_of_ast 0 amap cmap a in
  let amap, f = stack_term_of_ast 0 amap cmap f in
  let { max_arg = max; name2arg = l } = amap in
  let names = List.rev_map fst l in
  let env = Array.make max dummy in
  if f = truec then
   Fmt.eprintf "@[<hov 1>%a%a.@]\n%!"
     (pp_FOprolog names env) a
     (pplist (pp_FOprolog names env) ",") (split_conj f)
  else
   Fmt.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
     (pp_FOprolog names env) a
     (pplist (pp_FOprolog names env) ",") (split_conj f)) p*)
;;*)

let rec pp_FOprolog p = 
 List.iter
  (function
      Local _
    | Mode _
    | Begin
    | Constraint _
    | Chr _
    | Macro _
    | Type _
    | End -> assert false (* TODO *)
    | Accumulated l -> pp_FOprolog l
    | Clause { Elpi_ast.body = t } ->
       (* BUG: ConstMap.empty because "local" declarations are ignored ATM *)
       let t = term_of_ast 0 t in
       match t with
       | App(_, Custom _, _) | App(_,_,(Custom _)::_) -> ()  
       | App(hd,a,[f]) when hd == rimplc -> 
         Fmt.eprintf "@[<hov 1>%a@ :-@ %a.@]\n%!"
          (prologppterm []) a
          (pplist (prologppterm []) ",") (split_conj f);
       | _ -> 
          Fmt.eprintf "@[<hov 1>%a.@]\n%!" (prologppterm []) t 
  ) p  
 ;;

 
let pp_prolog = pp_FOprolog
