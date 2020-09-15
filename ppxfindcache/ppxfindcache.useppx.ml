let () =
  let open Ppxfindcache_aux in
  let file, sha, cachefile, in_cache, ppx_args = common () in
  let argv = Array.concat [ [|Sys.executable_name;file;"--dump-ast";"--embed-errors"|] ; ppx_args ; ] in
  Migrate_parsetree.Driver.run_main ~argv ();
  flush_all ();
  if in_cache cachefile then begin
    let tmp = Filename.temp_file "" ".ppfindcache" in
    let tmpfd = Unix.(openfile tmp [O_WRONLY;O_SHARE_DELETE] 0o600) in
    Unix.dup2 tmpfd Unix.stdout;
    Printf.printf "%s#1 \"%s\"\n%!" sha file;
    let argv = Array.concat [ [|Sys.executable_name;file|] ; ppx_args ] in
    Migrate_parsetree.Driver.run_main ~argv ();
    flush_all ();
    Unix.close tmpfd;
    let o = open_out cachefile in
    let text =
      let ch = open_in tmp in
      let r = read_file ch in
      close_in_noerr ch;
      r
    in
    let text = Re.(Str.global_replace (Str.regexp_string "Ppx_deriving_runtime") "Ppx_deriving_runtime_proxy" text) in
    output_fix o text 0 (String.length text);
    output_char o '\n';
    close_out o;
    Sys.remove tmp;
  end;
  exit 0
;;
