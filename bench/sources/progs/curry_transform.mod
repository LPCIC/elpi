/*
 * A program for transforming a function that takes two arguments as 
 * a pair into a function of two arguments; the second function is, thus
 * a curried version of the first. All of this computation is done through
 * higher-order unification and beta reduction (for substitution)
 */

module  curry_transform.

type  curry  tm -> tm -> o.

curry  (fix F \ (abs X \ (A (fst X) (snd X) (prp X)
                             (R \ S \ (app F (pr R S))))))
       (fix F \ (abs Y \ (abs Z \ (A Y Z truth
                                   (R \ S \ (app (app F R) S)))))).


