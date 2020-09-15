let read_file f =
  let b = Buffer.create 500 in
  begin
    try while true do Buffer.add_channel b f 1; done
    with End_of_file -> ()
  end;
  Buffer.contents b
;;

let rec find_matching s i depth =
  if s.[i] = ')' && depth = 1 then i
  else if s.[i] = ')' then find_matching s (i+1) (depth-1)
  else if s.[i] = '(' then find_matching s (i+1) (depth+1)
  else find_matching s (i+1) depth
;;

let rec output_fix f s i j =
  if i = j then ()
  else
    try
      if String.sub s i 9 = "let rec (" then
        let stop = find_matching s i 0 in
        Printf.fprintf f "let rec %s" (String.sub s (i+9) (stop - (i + 9)));
        output_fix f s (stop+1) j
      else raise Not_found
    with _ ->
      output_char f s.[i];
      output_fix f s (i+1) j

let exec ?(err=fun _ -> false, "") p args =
  let tmp_out = Filename.temp_file "" ".ppxfindcache" in
  let out = Unix.openfile tmp_out [Unix.O_WRONLY] 0o600 in
  let args = Array.append [|p|] args in
  let pid = Unix.create_process p args Unix.stdin out Unix.stderr in
  Unix.close out;
  let _, exit = Unix.waitpid [] pid in
  let out = open_in tmp_out in
  let s = read_file out in
  close_in out;
  Sys.remove tmp_out;
  match exit with
  | Unix.WEXITED 0 -> true, s
  | _ -> err s

let must (b,s) =
  if b then s else exit 1

let path_sanitize s = String.map (function '\\' -> '/' | x -> x) s

let common () =
  let file = ref "" in
  let flag = ref [||] in
  let cache = ref [] in
  let () =
    let open Arg in
    parse [
      "--dep", String (fun s -> Printf.eprintf "skip %s\n" s), "ignored";
      "--ppx-opt", String (fun s -> flag := Array.append !flag [|s|]), "option for the ppx rewriter";
      "--cache-file", String (fun s -> cache := path_sanitize s :: !cache), "files for which a cache is stored";
    ] (fun x -> file := x) "usage"
    in
  let file = !file in
  let flag = !flag in
  let cache x = List.mem (path_sanitize x) !cache in

  let sha = Digest.file file |> Digest.to_hex in
  let sha = Printf.sprintf "(*%s %s %s*)\n" sha file (String.concat " " (Array.to_list flag)) in

  let cachefile =
    let open Filename in
    let dir, file = dirname file, basename file in
    let cachedir = concat dir ".ppcache" in
    (try Unix.mkdir cachedir 0o700 with Unix.Unix_error _ -> ());
    concat cachedir file in

  file, sha, cachefile, cache, flag
;;
