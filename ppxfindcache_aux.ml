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

let main use_ppx =
  let ppx = ref "" in
  let file = ref "" in
  let flag = ref [||] in
  let cache = ref [] in
  let () =
    let open Arg in
    parse [
      "--dep", String (fun s -> Printf.eprintf "skip %s\n" s), "ignored";
      "--ppx", Set_string ppx, "list of ppx, glued using , (eg foo,bar,baz)";
      "--ppx-opt", String (fun s -> flag := Array.append !flag [|s|]), "option for the ppx rewriter";
      "--cache-file", String (fun s -> cache := s :: !cache), "files for which a cache is stored";
    ] (fun x -> file := x) "usage"
    in
  let ppx = !ppx in
  let file = !file in
  let flag = !flag in
  let cache = !cache in

  let sha = must @@ exec "sha1sum" [|file|] in
  let sha = String.sub sha 0 (String.length sha - 1) in
  let sha = Printf.sprintf "(*%s %s %s*)\n" sha ppx (String.concat " " (Array.to_list flag)) in

  let cachefile =
    let open Filename in
    let dir, file = dirname file, basename file in
    let cachedir = concat dir ".ppcache" in
    (try Unix.mkdir cachedir 0o700 with Unix.Unix_error _ -> ());
    concat cachedir file in

  let all_ppx_available =
    let open List in
    let ppx = String.split_on_char ',' ppx in
    fold_left (&&) true
      (ppx
        |> map (fun x -> exec "ocamlfind" [|"query";"-qo";x|])
        |> map fst) in

  if use_ppx then
    let () = if not all_ppx_available then (Printf.eprintf "some ppx not available"; exit 1) in
    let args =
      let open Array in
      append [|ppx|] (append flag [|file|]) in
    let binary = must @@ exec "ppxfind" (Array.append args [|"--as-pp"|]) in
    let text = must @@ exec "ppxfind" args in
    if List.mem cachefile cache then begin
      let o = open_out cachefile in
      Printf.fprintf o "%s#1 \"%s\"\n" sha file;
      output_fix o text 0 (String.length text);
      output_char o '\n';
      close_out o;
    end;
    output_string stdout binary
  else
    let h, header = exec "head" [|"-1";cachefile|] in
    if header = sha then
      output_string stdout @@ read_file (open_in cachefile)
    else begin
      Printf.eprintf "No ppx and no %s cache file for %s"
        (if h then "matching" else "") file;
      exit 1
    end
;;