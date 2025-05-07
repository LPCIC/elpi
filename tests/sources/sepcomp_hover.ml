let p1 = {|
  p 2 :- p 1.
|}

let maine = {|
pred p o:int.
p 1.
main :- p X, X = X.
|}

open Elpi.API

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let pmain,unit0 = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 1 maine in
  let _,unit1 = cc ~elpi ~flags ~base:pmain 2 p1 in

  let h0 = Compile.hover unit0 in
  let h1 = Compile.hover unit1 in

  let mkloc u n m =
    let l = Ast.Loc.initial (Printf.sprintf "<u%d>" u) in
    { l with Ast.Loc.source_start = n; source_stop = m } in

  let text_of_loc s { Ast.Loc.source_start = n; source_stop = m } =
    String.sub s n (m-n) in

  (* Format.printf "unit 1\n%a\n" (Compile.IntervalTree.pp Compile.pp_info) h0;
  Format.printf "unit 2\n%a\n" (Compile.IntervalTree.pp Compile.pp_info) h1; *)

  let loc_x = mkloc 1 33 34 in
  let loc_comma = mkloc 1 31 32 in
  let loc_p = mkloc 1 28 29 in

  let inspect loc =
    Format.printf "@[<v>info for '%s'@,%a@]" (text_of_loc maine loc)
      (RawPp.list (fun fmt (x,y) -> Format.fprintf fmt "%s@,%a@," (text_of_loc maine x) Compile.pp_info y) "") (Compile.IntervalTree.find loc h0) in

  inspect loc_x;
  inspect loc_comma;
  inspect loc_p;



