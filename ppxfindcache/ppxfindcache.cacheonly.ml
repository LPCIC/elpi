let () =
  let open Ppxfindcache_aux in
  let file, sha, cachefile, in_cache, _ = common () in
  let _h, header = exec "head" [|"-1";cachefile|] in
  if in_cache cachefile then
    if header = sha then begin
      output_string stdout @@ read_file (open_in cachefile);
      exit 0
    end else begin
     Printf.eprintf "Cache file for %s does not match" file;
     output_string stdout @@ read_file (open_in cachefile);
      exit 0
    end
  else begin
      Printf.eprintf "No cache file %s for %s" cachefile file;
      exit 1
  end
;;