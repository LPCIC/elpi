
open Elpi.Internal.Discrimination_tree
let () = assert (k_of (mkConstant ~safe:false ~data:~-17 ~arity:0) == kConstant)
let () = assert (k_of mkVariable == kVariable)
let () = assert (k_of mkOther == kOther)
let () =
  let open Elpi.API in
  match RawData.look ~depth:0 (RawOpaqueData.of_int 4) with
  | RawData.CData c ->
      assert (k_of (mkPrimitive (Obj.magic c)) == kPrimitive)
  | _ -> assert false
  
let () = assert (arity_of (mkConstant ~safe:false ~data:~-17 ~arity:3) == 3)
let () = assert (arity_of mkVariable == 0)
let () = assert (arity_of mkOther == 0)
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

  