/*
 * Code for recognizing tail recursive functions of two arguments.
 * This program illustrates the power of higher-order unification.
 */

module tr_recognizer.

type  tl_rec  tm -> o.

tl_rec (fix F\ (abs X\ (abs Y\ (H X Y)))).

tl_rec (fix F\ (abs X\ (abs Y\ (app (app F (G X Y)) (H X Y))))).

tl_rec (fix F\ (abs X\ (abs Y\ 
                  (cond (C X Y) (H F X Y) (G F X Y))))) :-
       tl_rec (fix F\ (abs X\ (abs Y\ (H F X Y)))),
       tl_rec (fix F\ (abs X\ (abs Y\ (G F X Y)))).



