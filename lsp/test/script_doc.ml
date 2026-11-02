open Test_lsp_lib

(* documentation and previews: the comment block on the line before a
   declaration is shown on hover (not one separated by a blank line); a
   definition is previewed with the rules that follow its declaration (only
   blank space in between), up to 8 lines; a comment after code on its line
   is not documentation, but the line comment right after the full stop of a
   declaration documents it, when no comment comes before it *)
let () = register ~name:"doc" "doc.elpi" (fun file ->
  open_file file;
  hover file "twice 21" 0;
  definition file "twice 21" 0;
  hover file "undocumented _" 0;
  definition file "undocumented _" 0;
  hover file "main :-" 0;
  definition file "main :-" 0;
  (* comments after code on their line are not documentation *)
  hover file "qa, ph" 0;
  hover file "ph, pb" 0;
  hover file "pb 1" 0;
  (* a line comment after the full stop of a declaration documents it, when
     no comment comes before it; also in builtin.elpi *)
  hover file "pg, pc" 0;
  hover file "pc red" 0;
  hover file "red, pd" 0;
  hover file "pd, print" 0;
  hover file "green blue" 0;
  hover file "blue gray" 0;
  hover file "gray a" 0;
  hover file "a b ok" 0;
  hover file "b ok" 0;
  hover file "ok." 0)
