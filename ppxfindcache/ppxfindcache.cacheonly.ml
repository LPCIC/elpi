let () =
  let open Ppxfindcache_aux in
  let file, sha, cachefile, cache, _ = common () in
  let h, header = exec "head" [|"-1";cachefile|] in
  if List.mem cachefile cache && header = sha then begin
      output_string stdout @@ read_file (open_in cachefile);
      exit 0
  end else begin
      Printf.eprintf "No ppx and no %s cache file for %s"
      (if h then "matching" else "") file;
      exit 1
  end
;;