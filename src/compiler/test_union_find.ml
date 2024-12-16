open Elpi_compiler.Union_find

module M = Make (struct
  include Int

  let hash x = x
  let pp _ _ = () 
end)

open M

let _ =
  (* Partition avec 9 classes (qui sont des singletons) *)
  let uf = create () in
  
  for i = 1 to 8 do
    add uf i
  done;

  (* Partition avec 4 classes disjointes obtenue après
     Union(1, 2), Union(3, 4), Union(2, 5), Union(1, 6) et Union(2, 8). *)
  union uf (1, 2);
  union uf (3, 4);
  union uf (2, 5);

  let uf1 = do_open (do_close uf) in

  union uf (1, 6);
  union uf (2, 8);
  assert (roots uf |> List.length = 3);
  (* The cloned table is not impacted by the modification in uf *)
  (* uf should be: https://fr.wikipedia.org/wiki/Union-find#/media/Fichier:Dsu_disjoint_sets_final.svg *)
  assert (roots uf1 |> List.length = 5);
  union uf1 (1, 6);
  assert (roots uf1 |> List.length = 4);
  assert (roots uf |> List.length = 3)
