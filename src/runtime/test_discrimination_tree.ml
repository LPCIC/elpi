open Elpi_runtime.Discrimination_tree
module DT = Elpi_runtime.Discrimination_tree
open Internal

let test ~expected found = 
  if expected <> found then failwith (Format.asprintf "Test DT error: Expected %d, but found %d" expected found)


let () = assert (k_of (mkConstant ~safe:false ~data:~-17 ~arity:0) == kConstant)
let () = assert (k_of mkVariable == kVariable)
let () = assert (k_of mkAny == kOther)
let () =
  let c = Elpi_runtime.Data.C.in_int 4 in
  assert (k_of (mkPrimitive (Obj.magic c)) == kPrimitive)
  
let () = assert (arity_of (mkConstant ~safe:false ~data:~-17 ~arity:3) == 3)
let () = assert (arity_of mkVariable == 0)
let () = assert (arity_of mkAny == 0)
let () = assert (arity_of mkInputMode == 0)
let () = assert (arity_of mkOutputMode == 0)
let () = assert (arity_of mkListTailVariable == 0)
let () = assert (arity_of mkListHead == 0)
let () = assert (arity_of mkListEnd == 0)
let () =
  let c = Elpi_runtime.Data.C.in_int 4 in
  assert (arity_of (mkPrimitive (Obj.magic c)) == 0)

(* let () = Printf.eprintf "%x %x %x\n" mkInputMode data_mask (data_of mkInputMode) *)
let () = assert (data_of mkInputMode == 1)
let () = assert (data_of mkOutputMode == 2)
let () = assert (data_of mkListTailVariable == 3)
let () = assert (data_of mkListHead == 4)
let () = assert (data_of mkListEnd == 5)

let () = 
  let mkName i = mkConstant ~safe:false ~data:i ~arity:0 in (* bound names *)
  
  let constA = mkConstant ~safe:false ~data:~-1 ~arity:~-0 in (* a *)
  let constF = mkConstant ~safe:false ~data:~-2 ~arity:~-1 in (* f *)

  let test_nb = ref 1 in
  
  let test (pathInsts: (cell list * int) list) (pathGoal,_) mode nb =
    Printf.printf "\n-> Running test %d <-\n" !test_nb; incr test_nb;
    let pathGoal = Path.of_list (mode :: pathGoal @ [mkPathEnd]) in
    (* Format.printf "%a\n" pp_path pathGoal; *)
    let pathInsts = List.map (fun (x,y) -> x @ [mkPathEnd], y) pathInsts in
    let add_to_trie t (key,value) = 
      index t (Path.of_list key) ~max_list_length:1000 value in
    let trie = List.fold_left add_to_trie (empty_dt []) pathInsts in 
    let retrived = retrieve (fun x y -> y - x) pathGoal trie in
    let retrived_nb = Elpi_runtime.Bl.length retrived in 
    Format.printf " Retrived clause number is %d\n%!" retrived_nb;
    (* let pp_sep = fun f _ -> Format.pp_print_string f " " in *)
    (* Format.printf " Found instances are %a\n%!" (Format.pp_print_list ~pp_sep Format.pp_print_int) retrived; *)
    test ~expected:retrived_nb nb;
    if (Elpi_runtime.Bl.to_list retrived |> List.sort Int.compare |> List.rev) <> (retrived |> Elpi_runtime.Bl.to_list) then failwith "Test DT error: resultin list is not correctly ordered"
  in
  
  let p1 = [mkListHead; constA; mkListTailVariable; constA], 1 in                                         (* 1: [a | _] a *)
  let p2 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; mkListEnd; constA], 2 in                    (* 2: [a,x0,x1,x3] a *)
  let p3 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; mkListEnd; mkVariable], 3 in                (* 3: [a,x0,x1,x3] X *)
  let p4 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; constA; mkListEnd], 4 in                    (* 4: [a,x0,x1,x3,a] *)
  let p5 = [mkAny; mkVariable], 5 in                                                                    (* 5: (x\ ...) X *)
  let p6 = [mkListHead; constF; mkListHead; mkName 1; mkName 2; mkListTailVariable; constA; mkListEnd], 6 in (* 6: [f [x1, x2 | _] a] f *)
  let p7 = [mkListHead; constA; mkVariable; mkListEnd; constA], 7 in                                      (* 7: [a,X] a *)
  let p8 = [mkListHead; constA; mkName 0; mkListEnd; mkVariable], 8 in                                    (* 8: [a,x0] X *)

  test [p2; p3; p4; p5; p6] p1 mkOutputMode 3;
  test [p2; p3; p4; p5; p6] p1 mkInputMode 1;
  test [p1; p2; p3; p4; p5; p6; p8] p7 mkOutputMode 3;
  test [p1; p2; p3; p4; p5; p6; p8] p7 mkInputMode 2

let () =  
  let get_length dt path = DT.retrieve compare path !dt |> Elpi_runtime.Bl.length in
  let remove dt e = dt := DT.remove (fun x -> x = e) !dt in
  let index dt path v = dt := DT.index !dt path ~max_list_length:1000 v in 

  let constA = mkConstant ~safe:false ~data:~-1 ~arity:~-0 in (* a *)
  let p1 = [mkListHead; constA; mkListTailVariable; constA] in
  let p2 = [mkListHead; constA; mkListTailVariable; constA; constA] in
  
  let p1Index = Path.of_list p1 in (* path for indexing *)
  let p1Retr = mkInputMode :: p1 |> Path.of_list in (* path for retrival *)

  let p2Index = Path.of_list p2 in (* path for indexing *)
  let p2Retr = mkInputMode :: p2 |> Path.of_list in (* path for retrival *)

  let dt = DT.empty_dt (List.init 0 Fun.id) |> ref in
  index dt p1Index 100; index dt p1Index 200;
  index dt p2Index 200; index dt p2Index 200;

  Printf.printf "Test remove 1\n";
  test ~expected:2 (get_length dt p1Retr);
  test ~expected:2 (get_length dt p2Retr);

  Printf.printf "Test remove 2\n";
  remove dt 100;
  test ~expected:1 (get_length dt p1Retr);
  test ~expected:2 (get_length dt p2Retr);
  
  Printf.printf "Test remove 3\n";
  remove dt 100;
  test ~expected:1 (get_length dt p1Retr);

  Printf.printf "Test remove 4\n";
  remove dt 200;
  test ~expected:0 (get_length dt p1Retr)

(* Data.Global_symbols.bottom. A cell keeps only the low bits of a constant
   (data_mask), so two constants that differ by a multiple of data_mask + 1
   share a cell. The constants that can meet in an index are the negative
   ones (globals and program constants, >= bottom) and the bound variables
   (>= 0, < -bottom): they must all be distinct modulo data_mask + 1. If the
   layout of a cell changes, bottom must follow. *)
let bottom = Elpi_runtime.Data.Global_symbols.bottom
let cell c = mkConstant ~safe:false ~data:c ~arity:0

let () =
  (* the window [bottom, -bottom) is exactly data_mask + 1 integers wide *)
  assert (Int.equal (- bottom - bottom) (data_mask + 1));
  let extremes = [bottom; bottom + 1; -1; 0; 1; - bottom - 2; - bottom - 1] in
  extremes |> List.iteri (fun i c -> extremes |> List.iteri (fun j d ->
    if i < j && cell c == cell d then
      failwith (Printf.sprintf "Test DT error: constants %d and %d share a cell" c d)));
  extremes |> List.iter (fun c -> assert (k_of (cell c) == kConstant));
  (* one step outside the window shares a cell with the other end *)
  assert (cell (bottom - 1) == cell (- bottom - 1));
  assert (cell (- bottom) == cell bottom)

let () =
  (* the lowest global and the highest bound variable are told apart *)
  (* a rule is indexed by its path, a goal also starts with a mode *)
  let rule c = Path.of_list [cell c; mkPathEnd] in
  let goal c = Path.of_list [mkInputMode; cell c; mkPathEnd] in
  let keys = [bottom, 1; - bottom - 1, 2] in
  let dt = List.fold_left (fun t (c, v) -> index t (rule c) ~max_list_length:1000 v) (empty_dt []) keys in
  keys |> List.iter (fun (c, v) ->
    match Elpi_runtime.Bl.to_list (retrieve (fun x y -> y - x) (goal c) dt) with
    | [w] when Int.equal w v -> ()
    | l -> failwith (Printf.sprintf "Test DT error: constant %d retrieves %d rules, expected only rule %d" c (List.length l) v))

(* How a constant becomes a cell, on 64 bits (Sys.int_size = 63). A cell is an
   OCaml int; [bits] prints it from the highest bit, in four groups:

     kk aaaa s dddddddddddddddddddddddddddddddddddddddddddddddddddddddd
     |  |    | '-- 56 bits
     |  |    '-- bit 56, the highest bit of the data
     |  '-- 4 bits of arity (bits 57-60)
     '-- 2 bits of kind (bits 61-62): 00 constant, 01 primitive,
         10 variable, 11 other

   The shifts put the kind and the arity at their place:
     k_lshift  = Sys.int_size - 2     = 61
     ka_lshift = Sys.int_size - 2 - 4 = 57
   and the masks select a group:
     k_mask     = 3 lsl 61       11 0000 0 000...000
     arity_mask = 63 lsl 57      11 1111 0 000...000  (also covers the kind:
                                  arity_of uses it only when the kind is 00)
     data_mask  = 1 lsl 57 - 1   00 0000 1 111...111

   encode ~k ~arity ~data = (k lsl 61) lor (arity lsl 57) lor (data land data_mask)

   so [data land data_mask] keeps the low 57 bits of the constant and drops
   its 6 high bits, where the kind and the arity go. For a negative constant
   these 6 bits are copies of the sign, so nothing is lost as long as the
   constant is >= -2^57. What is lost is the sign itself: the data of a
   cell reads as a non-negative number, -15 comes back as 2^57 - 15. So -15
   and 2^57 - 15 would share a cell, and only one of them can be used.

   Data.Global_symbols.bottom = -2^56 picks which: the negative constants
   (globals, program constants) are >= -2^56 and have 1 in bit 56, the bound
   variables are < 2^56 and have 0 in bit 56. Bit 56 is what tells them apart
   (and why bottom is half of data_mask + 1, not all of it). *)
let bits n =
  let b = Buffer.create 70 in
  for i = Sys.int_size - 1 downto 0 do
    Buffer.add_char b (if (n lsr i) land 1 = 1 then '1' else '0');
    if i = k_lshift || i = ka_lshift || i = ka_lshift - 1 then Buffer.add_char b ' '
  done;
  Buffer.contents b

let cell_bits ?(arity = 0) c = bits (int_of_cell (mkConstant ~safe:false ~data:c ~arity))

let check what found expected =
  if not (String.equal found expected) then
    failwith (Printf.sprintf "Test DT error: %s is\n  %s\nexpected\n  %s" what found expected)

(* where the constants come from, see the layout in Data.Global_symbols *)
let () =
  let consc = Elpi_runtime.Data.Global_symbols.consc in
  let late = Elpi_runtime.Data.Global_symbols.declare_global_symbol "late_example" in
  (* static globals start just below the builtin predicates (-1 .. -11),
     late globals continue below them, program constants count up from bottom *)
  assert (consc < -11 && late < consc && bottom < late)

let () = if Int.equal Sys.int_size 63 then begin
  check "k_mask"     (bits k_mask)     "11 0000 0 00000000000000000000000000000000000000000000000000000000";
  check "arity_mask" (bits arity_mask) "11 1111 0 00000000000000000000000000000000000000000000000000000000";
  check "data_mask"  (bits data_mask)  "00 0000 1 11111111111111111111111111111111111111111111111111111111";

  (* a static global, like consc = -15: a negative int has all its high bits
     set; the 6 high bits are replaced by kind 00 and arity 0000 *)
  check "-15"             (bits (-15))           "11 1111 1 11111111111111111111111111111111111111111111111111110001";
  check "the cell of -15" (cell_bits (-15))      "00 0000 1 11111111111111111111111111111111111111111111111111110001";
  (* the same constant applied to 2 arguments: only the arity group changes *)
  check "the cell of -15 with arity 2" (cell_bits ~arity:2 (-15))
                                                 "00 0010 1 11111111111111111111111111111111111111111111111111110001";

  (* a late global, declared after Setup.init: just a lower negative number *)
  check "the cell of -17" (cell_bits (-17))      "00 0000 1 11111111111111111111111111111111111111111111111111101111";

  (* program constants: the lowest is bottom, then bottom + 1, ... *)
  check "bottom"          (bits bottom)          "11 1111 1 00000000000000000000000000000000000000000000000000000000";
  check "the cell of bottom + 3 with arity 1" (cell_bits ~arity:1 (bottom + 3))
                                                 "00 0001 1 00000000000000000000000000000000000000000000000000000011";

  (* a bound variable (the 6th binder): bit 56 is 0 *)
  check "the cell of 5"   (cell_bits 5)          "00 0000 0 00000000000000000000000000000000000000000000000000000101";

  (* below bottom, bit 56 becomes 0 and the cell is the one of a bound variable *)
  check "the cell of bottom - 1"  (cell_bits (bottom - 1))
                                                 "00 0000 0 11111111111111111111111111111111111111111111111111111111";
  check "the cell of -bottom - 1" (cell_bits (- bottom - 1))
                                                 "00 0000 0 11111111111111111111111111111111111111111111111111111111";

  (* cells that are not constants, for comparison *)
  check "mkInputMode" (bits (int_of_cell mkInputMode)) "11 0000 0 00000000000000000000000000000000000000000000000000000001";
  check "mkVariable"  (bits (int_of_cell mkVariable))  "10 0000 0 00000000000000000000000000000000000000000000000000000000"
end
