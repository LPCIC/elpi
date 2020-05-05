(* ppxfindcache is only considered as a proper dependency of
   pps by dune if the programs are public, but they should not be installed *)
let () =
  let file = Sys.argv.(1) in
  let i = open_in file in
  let l = ref [] in
  try
    while true do
      l := (input_line i ^ "\n") :: !l
    done
  with _ ->
    close_in i;
    let rex = Re.Str.regexp ".*bin/ppxfindcache_.*" in
    let l1 = List.filter (fun x -> not (Re.Str.string_match rex x 0)) !l in
    let o = open_out file in
    List.iter (output_string o) (List.rev l1);
    Printf.eprintf "done pruning %d lines\n" (List.length !l - List.length l1);
    close_out o;
    exit 0