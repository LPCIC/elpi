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

let main () =
  let ppx = Sys.argv.(1) in
  let file = Sys.argv.(2) in
  let flag = if Array.length Sys.argv > 3 then Sys.argv.(3) else "" in

  let sha = must @@ exec "sha1sum" [|file|] in
  let sha = String.sub sha 0 (String.length sha - 1) in
  let sha = Printf.sprintf "(*%s %s %s*)" sha Sys.argv.(1) flag in

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

   if all_ppx_available then
     let args =
       if flag = "" then [|ppx;file|] else [|ppx;flag;file|] in
     let binary = must @@ exec "ppxfind" (Array.append args [|"--as-pp"|]) in
     let text = must @@ exec "ppxfind" args in
     let o = open_out cachefile in
     Printf.fprintf o "%s\n#1 \"%s\"\n" sha file;
     output_fix o text 0 (String.length text);
     output_char o '\n';
     close_out o;
     output_string stdout binary
   else
     let _, header = exec "head" [|"-1";cachefile|] in
     if header = sha then
       output_string stdout @@ read_file (open_in cachefile)
     else
       exit 1
;;

main ()