let () =
  let open Ppxfindcache_aux in
  let file, sha, cachefile, cache, ppx_args = common () in
  let argv = Array.concat [ [|Sys.executable_name;file;"--dump-ast";"--embed-errors"|] ; ppx_args ; ] in
  Migrate_parsetree.Driver.run_main ~argv ();
  flush_all ();
  if List.mem cachefile cache then begin
    let tmp = Filename.temp_file "" ".ppfindcache" in
    let tmpfd = Unix.(openfile tmp [O_WRONLY] 00600) in
    Unix.dup2 tmpfd Unix.stdout;
    Printf.printf "%s#1 \"%s\"\n%!" sha file;
    let argv = Array.concat [ [|Sys.executable_name;file|] ; ppx_args ] in
    Migrate_parsetree.Driver.run_main ~argv ();
    flush_all ();
    Unix.close tmpfd;
    let o = open_out cachefile in
    let text = read_file (open_in tmp) in
    output_fix o text 0 (String.length text);
    output_char o '\n';
    close_out o;
    Sys.remove tmp;
  end;
  exit 0
;;