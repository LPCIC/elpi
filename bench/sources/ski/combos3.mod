module combos3.
accumulate combos2.

combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(K ((S S) K))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))).
combo "(((S I) ((K (K I)) (S ((((I I) S) S) I)))) ((I (K I)) K))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))))) (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (abs (x\ abs (y\ x))))).
combo "((I (K K)) (S K))" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "I" (abs (x\ x)).
combo "K" (abs (x\ abs (y\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((K K) (S S))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S (S (K (S I))))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))))).
combo "(S K)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))).
combo "(S (I K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))).
combo "(K (K I))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "I" (abs (x\ x)).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "((S I) (I ((K I) (I S))))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((I (S (((K ((S S) I)) I) I))) (I ((S (S (K I))) S)))" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (abs (x\ x))) (abs (x\ x))))) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((((S ((((S S) I) ((I S) S)) I)) (S K)) ((I S) (I (I K)))) K)" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ x))))))) (abs (x\ abs (y\ x)))).
combo "((I K) (S (I I)))" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ x))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((((K K) K) (S S)) S)" (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((S (I I)) S) K)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "((S K) (S S))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(((K K) ((K S) (K S))) (S (S I)))" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(K (((S S) (K S)) K))" (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ x))))).
combo "(((K K) K) S)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "I" (abs (x\ x)).
combo "((S K) (I (I S)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S (S ((I S) (I S)))) I) K)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(((I (S I)) I) (K I))" (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(((K S) ((S (K (I S))) I)) K)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ x)))) (abs (x\ abs (y\ x)))).
combo "((K (((I ((I K) (S S))) (S K)) K)) (K I))" (app (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "I" (abs (x\ x)).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "(K ((K (K S)) (I S)))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S K) ((S ((S (K S)) (I S))) I)) I)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ x)))) (abs (x\ x))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "((I K) I)" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))).
combo "((K (S S)) ((I (S K)) (I S)))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(I (I (S K)))" (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((K K) (((I K) I) ((I K) (((I I) I) K)))) K)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ x))))))) (abs (x\ abs (y\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((K K) (((K S) ((I K) K)) K))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x))))).
combo "((I S) (I K))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))).
combo "((K (K I)) ((K I) (S I)))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))).
combo "I" (abs (x\ x)).
combo "I" (abs (x\ x)).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "((K (S S)) (((K I) I) K))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ x))))).
combo "(I (S S))" (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(K (I (S (S S))))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((K S) K)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(((I ((K S) (S I))) I) ((S I) ((((S S) (((K I) S) K)) S) S)))" (app (app (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))) (abs (x\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S I) (K (K I))) ((S (I S)) (I ((K I) S))))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(((S K) K) (S (I S)))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "((K S) (((K K) I) I))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (abs (x\ x)))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "(S K)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))).
combo "((((S S) S) ((((K S) ((S S) (S (S S)))) S) K)) I)" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))) (abs (x\ x))).
combo "((((K K) I) ((K K) ((I K) S))) (I S))" (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(K (I ((((I K) S) (((K K) K) (I S))) K)))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (app (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ abs (y\ x)))))).
combo "(((I (I K)) I) I)" (app (app (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ x))) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((K ((((I I) (S I)) ((I K) I)) I)) K) ((K S) (((S S) ((S I) I)) (I (S K)))))" (app (app (app (abs (x\ abs (y\ x))) (app (app (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x)))) (abs (x\ x)))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ x)))) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "(((K ((K K) S)) (((S S) (I S)) (S K))) (((((((S S) K) K) I) S) K) S))" (app (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))) (app (app (app (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "((K S) I)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))).
combo "((I K) (I S))" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((I S) K)" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "(S ((K (K S)) S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).

