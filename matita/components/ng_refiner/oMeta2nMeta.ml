let convert_metasenv uri = 
  let new_metasenv, fixpoints =
    List.fold_left
      (fun (nm,fty) (i, ctx, ty) ->
         let new_ty, fix_ty = OCic2NCic.convert_term uri ty in

  in
  assert (fixpoints = []);
  new_metasenv
;;
