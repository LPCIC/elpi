module combos1.
accumulate randomlams.

combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K I) (((S (S K)) (S ((K K) (I I)))) (((K K) (I K)) K)))" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ x)))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x)))))).
combo "((((S (K (S I))) I) I) (((S I) I) S))" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))) (abs (x\ x))) (abs (x\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S (I ((I I) K)))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ x)))))).
combo "I" (abs (x\ x)).
combo "(S ((K S) S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((K S) ((S (S (K (I K)))) ((S S) (K (K I)))))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))))).
combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((S (S S)) (K (S I)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))).
combo "((S (S I)) I)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (abs (x\ x))).
combo "((S K) (I I))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ x)))).
combo "K" (abs (x\ abs (y\ x))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "((((K (I S)) S) ((K K) (((S K) K) (K (K S))))) (S (I K)))" (app (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))).
combo "I" (abs (x\ x)).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((I K) K)" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))).
combo "I" (abs (x\ x)).
combo "(S ((K (K S)) K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ x))))).
combo "((S (S S)) S)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S (((I S) I) S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((I K) ((K S) (S (S (S K)))))" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((S S) ((((K S) I) (S S)) (K S)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "I" (abs (x\ x)).
combo "((((S S) S) (K ((S S) (I (I (I K)))))) ((((K K) I) I) K))" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ x))))))))) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ x))))).
combo "((S I) K)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(((((K S) (I (I S))) (I (I (K K)))) S) ((S ((K (K S)) I)) ((I ((I S) S)) ((K K) I))))" (app (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x)))) (app (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x)))))).
combo "((K (I K)) S)" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((S (K ((I S) I))) K)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))))) (abs (x\ abs (y\ x)))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "((S ((I K) (K ((K S) S)))) K)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))) (abs (x\ abs (y\ x)))).
combo "((I I) S)" (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(I (K (K S)))" (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S S) S) S)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((((S K) (I ((I K) K))) K) I)" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ x)))) (abs (x\ x))).
combo "((I K) I)" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(((I I) (K K)) (K ((I (S K)) S)))" (app (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(I ((K I) K))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x))))).
combo "I" (abs (x\ x)).
combo "I" (abs (x\ x)).
combo "(K (((S (K I)) (S S)) ((K K) S)))" (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "I" (abs (x\ x)).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((I (S ((K I) (I S)))) S)" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(((I (K (I K))) ((((I S) S) K) (S I))) S)" (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))) (app (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "I" (abs (x\ x)).
combo "(S (S S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(K ((K (I I)) S))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "I" (abs (x\ x)).
combo "(((I K) I) (S K))" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "I" (abs (x\ x)).
combo "(S ((K K) ((S ((I I) (I ((I K) K)))) (I (K I)))))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))))) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x))))))).
combo "((S K) (S K))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((S (I K)) S)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "I" (abs (x\ x)).
combo "(I (I S))" (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((K S) K) (S S))" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "((I (I S)) (S ((K S) I)))" (app (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))))).
combo "((S ((K K) (S ((K S) S)))) (K (I K)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))).
combo "I" (abs (x\ x)).
combo "((I S) (I ((S S) I)))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "((((K I) (K K)) S) ((I (((K (I K)) K) S)) ((S (K I)) ((((((I S) I) S) S) (((S I) S) (((K I) (S (K S))) (I (I ((S K) K)))))) I))))" (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ x)) (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (app (app (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ x)) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))))))) (abs (x\ x)))))).
combo "(I (S K))" (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((S (S I)) (K (S ((S K) I))))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ x)))))).
combo "(I (S K))" (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "(S ((S K) (((K ((I S) K)) (K K)) ((K I) S))))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(K (I (I S)))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "(S (S K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "I" (abs (x\ x)).
combo "K" (abs (x\ abs (y\ x))).
combo "(I ((K I) (I (S I))))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))))).
combo "((K I) (I S))" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((((S S) (S I)) (K (I K))) (S (((S K) I) (K S))))" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(((((I I) S) I) ((I S) (K (S K)))) (I I))" (app (app (app (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))))) (app (abs (x\ x)) (abs (x\ x)))).
combo "K" (abs (x\ abs (y\ x))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "((K I) K)" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "K" (abs (x\ abs (y\ x))).
combo "((S I) (S K))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))).
combo "((K I) K)" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "(S (S ((K K) S)))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(K (I S))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S (K (((S S) (((S S) I) K)) ((I I) (K K)))))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (abs (x\ abs (y\ x))))) (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))))).
combo "(((I S) (((S (I S)) S) S)) I)" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x))).
combo "(S ((S (S (K I))) S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(I ((K K) I))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x)))).
combo "((K (S K)) (((I ((I S) ((K S) (K I)))) K) ((K (S ((K ((((I (I I)) I) K) S)) K))) K)))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (app (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (app (app (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ x)))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ x)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((K (S (((I (S S)) I) I))) (S ((K ((I K) ((S I) S))) K))) K)" (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x))) (abs (x\ x))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ x)))).
combo "(((I K) ((S K) (I S))) (S I))" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))).
combo "(K ((S (K S)) K))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ x))))).
combo "((K K) K)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))).
combo "I" (abs (x\ x)).
combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K I) (S ((I S) (S (S K)))))" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))))).
combo "((I S) ((K (((I K) K) K)) (I K)))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))).
combo "(K (K S))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K K) S)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(K ((K K) K))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))).
combo "(I ((S K) (S S)))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "((S (I (((S I) S) K))) ((S I) (((K S) S) S)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(I ((I S) I))" (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(K ((I (I S)) S))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((I K) K)" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((S K) (S S)) ((S S) K))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "((S (K I)) ((S ((I S) S)) ((I I) I)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ x))))).
combo "((S K) ((((I (I K)) (I S)) (I (S (S K)))) S))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (app (app (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((I S) S)" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K S) K)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(((K S) (I I)) K)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (abs (x\ x)))) (abs (x\ abs (y\ x)))).
combo "((S I) K)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(((S I) K) ((I K) (I K)))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))).
combo "((I (S K)) K)" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x)))).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "K" (abs (x\ abs (y\ x))).
combo "I" (abs (x\ x)).
combo "(((K I) K) S)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S K)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))).
combo "(((S I) (I (S K))) ((I I) ((S ((I S) I)) (I ((K K) S)))))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))) (app (app (abs (x\ x)) (abs (x\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))))).
combo "((S I) S)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "((K (S (K I))) K)" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))) (abs (x\ abs (y\ x)))).
combo "((K I) S)" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "I" (abs (x\ x)).
combo "((I ((I I) I)) (I (I S)))" (app (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ x)))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "((I S) K)" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(I ((S S) S))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "I" (abs (x\ x)).
combo "(K (K S))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S ((I K) K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))).
combo "I" (abs (x\ x)).
combo "((K ((K S) I)) (S S))" (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((I K) (K I))" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "K" (abs (x\ abs (y\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(K (I S))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "I" (abs (x\ x)).
combo "(((I K) I) (I I))" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (abs (x\ x)) (abs (x\ x)))).
combo "(K (K S))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(K (I K))" (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))).
combo "I" (abs (x\ x)).
combo "((K (I (I (K I)))) S)" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(S (I K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "((S K) (((I S) I) (((I I) (K I)) (I S))))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "((((S K) K) S) S)" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((((I (S I)) (K (K ((S K) K)))) (((S I) ((K S) I)) (I K))) ((K K) (K I)))" (app (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))).
combo "K" (abs (x\ abs (y\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "I" (abs (x\ x)).
combo "((S ((S ((K (K I)) I)) I)) (K K))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (abs (x\ x)))) (abs (x\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((K (S ((I S) I))) (((I (S K)) I) ((I (K S)) ((S ((K I) I)) I))))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))))) (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (abs (x\ x))) (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ x)))) (abs (x\ x)))))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(((I I) ((S K) K)) (K ((K S) (S I))))" (app (app (app (abs (x\ x)) (abs (x\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x))))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))))).
combo "((S K) ((((K (S S)) K) S) (K I)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ x))))).
combo "I" (abs (x\ x)).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((I S) (S ((((K I) K) I) (K (((I (K (I K))) S) I)))))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))))))).
combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((I I) I)" (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "(((K ((S (I S)) S)) I) (S S))" (app (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((I S) S)" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((S I) (K (K (I S))))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "((S I) I)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ x))).
combo "(I ((K (K (K (S (I (((((S ((I S) I)) K) K) ((K S) K)) K)))))) K))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (app (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x))))))))) (abs (x\ abs (y\ x))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((I S) ((S K) (I K)))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))).
combo "(I (S (S S)))" (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "(K ((K (S K)) (I I)))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (abs (x\ x)) (abs (x\ x))))).
combo "(((S I) I) S)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K (((I S) ((K ((K S) S)) (K ((I S) (K K))))) (I I))) I)" (app (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))))) (app (abs (x\ x)) (abs (x\ x))))) (abs (x\ x))).
combo "((K S) (I (K (((S S) I) I))))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (abs (x\ x)))))).
combo "((((I I) S) ((S I) (S S))) S)" (app (app (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((K K) (I (K (K I))))" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))))).
combo "((S S) K)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))).
combo "(((K I) (S I)) K)" (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (abs (x\ abs (y\ x)))).
combo "I" (abs (x\ x)).
combo "K" (abs (x\ abs (y\ x))).
combo "(((I (K S)) S) (((I (I (I (I (K K))))) (S K)) ((K (S S)) I)))" (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x))))).
combo "(I S)" (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(S K)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))).
combo "((((I S) K) S) ((I K) S))" (app (app (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(I I)" (app (abs (x\ x)) (abs (x\ x))).
combo "K" (abs (x\ abs (y\ x))).
combo "(((K (S ((S K) K))) S) ((K (K (K S))) S))" (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "((K (I K)) ((K I) I))" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ x)))).
combo "(S S)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(S (((I K) (K S)) S))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(K ((I K) I))" (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x)))).
combo "(I ((S S) I))" (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "((K ((K (K ((S I) (K I)))) (K K))) (I S))" (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "(S I)" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))).
combo "(I (I (I S)))" (app (abs (x\ x)) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S I) (S I)) S)" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "(((I K) K) (S I))" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))).
combo "((K (K K)) I)" (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ x))).
combo "(K K)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((((K I) (I ((I I) K))) K) (I S)) ((K K) (S (I S))))" (app (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ x)))))) (abs (x\ abs (y\ x)))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "((I K) (K S))" (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((I (K K)) I)" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(K S)" (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "((I S) (K (S K)))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ x)))))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "((S S) (I (I S)))" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ x)) (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(((S S) I) (I (K I)))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((((K I) S) (K (K K))) I) K)" (app (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "I" (abs (x\ x)).
combo "(S (K I))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "(((((S S) S) K) (((I (K K)) I) I)) I)" (app (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ x)))) (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ x))) (abs (x\ x)))) (abs (x\ x))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((((S S) ((S (K K)) (I K))) I) ((I S) (K (S ((((K I) (I K)) K) ((((K (S ((I ((S S) I)) ((I I) (K K))))) (K K)) S) S)))))) ((K ((K S) (K K))) ((I ((((K S) I) (K I)) I)) I)))" (app (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (app (abs (x\ x)) (abs (x\ abs (y\ x)))))) (abs (x\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ x)) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x)))) (app (app (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x)))) (app (app (abs (x\ x)) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))))) (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))) (app (app (abs (x\ x)) (app (app (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (abs (x\ x)))) (abs (x\ x))))).
combo "(I K)" (app (abs (x\ x)) (abs (x\ abs (y\ x)))).
combo "((K I) (K (K S)))" (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))))).
combo "(K (K ((K S) ((S S) S))))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))))).
combo "((I S) (K I))" (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "K" (abs (x\ abs (y\ x))).
combo "((((S (K I)) K) I) K)" (app (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (abs (x\ abs (y\ x)))) (abs (x\ x))) (abs (x\ abs (y\ x)))).
combo "(((S I) ((K I) S)) (I I))" (app (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))) (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ x)) (abs (x\ x)))).
combo "(((I K) I) ((K ((I S) S)) I))" (app (app (app (abs (x\ x)) (abs (x\ abs (y\ x)))) (abs (x\ x))) (app (app (abs (x\ abs (y\ x))) (app (app (abs (x\ x)) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (abs (x\ x)))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(((I (S ((S S) (S (S I))))) (((K I) K) I)) S)" (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x))))))) (app (app (app (abs (x\ abs (y\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
combo "K" (abs (x\ abs (y\ x))).
combo "((I (S S)) (K (K K)))" (app (app (abs (x\ x)) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))))).
combo "(K I)" (app (abs (x\ abs (y\ x))) (abs (x\ x))).
combo "(K (S (I I)))" (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ x)) (abs (x\ x))))).
combo "S" (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))).
combo "(S (K I))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ x)))).
combo "((K K) I)" (app (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x)))) (abs (x\ x))).
combo "(S (S I))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (abs (x\ x)))).
combo "(S ((I ((I (K I)) K)) K))" (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (app (abs (x\ x)) (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ x))))).
combo "((K ((((I I) I) K) S)) ((K (K (K (((I (K I)) (K S)) ((I I) K))))) S))" (app (app (abs (x\ abs (y\ x))) (app (app (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ x))) (abs (x\ abs (y\ x)))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (abs (x\ abs (y\ x))) (app (app (app (abs (x\ x)) (app (abs (x\ abs (y\ x))) (abs (x\ x)))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))) (app (app (abs (x\ x)) (abs (x\ x))) (abs (x\ abs (y\ x)))))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))))).
combo "I" (abs (x\ x)).
combo "((S (K K)) S)" (app (app (abs (x\ abs (y\ abs (z\ app (app x z) (app y z))))) (app (abs (x\ abs (y\ x))) (abs (x\ abs (y\ x))))) (abs (x\ abs (y\ abs (z\ app (app x z) (app y z)))))).
