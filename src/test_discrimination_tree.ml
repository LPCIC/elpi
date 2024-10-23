open Elpi.Internal.Discrimination_tree
module DT = Elpi.Internal.Discrimination_tree
open Internal

let test ~expected found = 
  if expected <> found then failwith (Format.asprintf "Test DT error: Expected %d, but found %d" expected found)


let () = assert (k_of (mkConstant ~safe:false ~data:~-17 ~arity:0) == kConstant)
let () = assert (k_of mkVariable == kVariable)
let () = assert (k_of mkLam == kOther)
let () =
  let open Elpi.API in
  match RawData.look ~depth:0 (RawOpaqueData.of_int 4) with
  | RawData.CData c ->
      assert (k_of (mkPrimitive (Obj.magic c)) == kPrimitive)
  | _ -> assert false
  
let () = assert (arity_of (mkConstant ~safe:false ~data:~-17 ~arity:3) == 3)
let () = assert (arity_of mkVariable == 0)
let () = assert (arity_of mkLam == 0)
let () = assert (arity_of mkInputMode == 0)
let () = assert (arity_of mkOutputMode == 0)
let () = assert (arity_of mkListTailVariable == 0)
let () = assert (arity_of mkListHead == 0)
let () = assert (arity_of mkListEnd == 0)
let () =
  let open Elpi.API in
  match RawData.look ~depth:0 (RawOpaqueData.of_int 4) with
  | RawData.CData c ->
      assert (arity_of (mkPrimitive (Obj.magic c)) == 0)
  | _ -> assert false

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
    let retrived_nb = Elpi.Internal.Bl.length retrived in 
    Format.printf " Retrived clause number is %d\n%!" retrived_nb;
    (* let pp_sep = fun f _ -> Format.pp_print_string f " " in *)
    (* Format.printf " Found instances are %a\n%!" (Format.pp_print_list ~pp_sep Format.pp_print_int) retrived; *)
    test retrived_nb nb;
    if (Elpi.Internal.Bl.to_list retrived |> List.sort Int.compare |> List.rev) <> (retrived |> Elpi.Internal.Bl.to_list) then failwith "Test DT error: resultin list is not correctly ordered"
  in
  
  let p1 = [mkListHead; constA; mkListTailVariable; constA], 1 in                                         (* 1: [a | _] a *)
  let p2 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; mkListEnd; constA], 2 in                    (* 2: [a,x0,x1,x3] a *)
  let p3 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; mkListEnd; mkVariable], 3 in                (* 3: [a,x0,x1,x3] X *)
  let p4 = [mkListHead; constA; mkName 0; mkName 1; mkName 2; constA; mkListEnd], 4 in                    (* 4: [a,x0,x1,x3,a] *)
  let p5 = [mkLam; mkVariable], 5 in                                                                    (* 5: (x\ ...) X *)
  let p6 = [mkListHead; constF; mkListHead; mkName 1; mkName 2; mkListTailVariable; constA; mkListEnd], 6 in (* 6: [f [x1, x2 | _] a] f *)
  let p7 = [mkListHead; constA; mkVariable; mkListEnd; constA], 7 in                                      (* 7: [a,X] a *)
  let p8 = [mkListHead; constA; mkName 0; mkListEnd; mkVariable], 8 in                                    (* 8: [a,x0] X *)

  test [p2; p3; p4; p5; p6] p1 mkOutputMode 3;
  test [p2; p3; p4; p5; p6] p1 mkInputMode 1;
  test [p1; p2; p3; p4; p5; p6; p8] p7 mkOutputMode 3;
  test [p1; p2; p3; p4; p5; p6; p8] p7 mkInputMode 2

let () =  
  let get_length dt path = DT.retrieve compare path !dt |> Elpi.Internal.Bl.length in
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
