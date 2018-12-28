% Some example (encodings of) functions in the functional programming 
% language

module terms.

trm trfact1 (fix F \ (abs N\ (abs M\
             (cond (eq N (c 0)) M 
                   (app (app F (minus N (c 1))) (times N M)))))).

trm trfact2 (fix F \ (abs P \ 
             (cond (&& (prp P) (eq (fst P) (c 0))) (snd P)
                   (cond (prp P) (app F (pr (minus (fst P) (c 1))
                                            (times (fst P) (snd P))))
                          err)))).



trm gcd2 (fix Gcd\ (abs X\ (abs Y\ 
                       (cond (eq (c 1) X) (c 1)
                             (cond (lss X Y) ((app (app Gcd Y) X))
                                   (cond (eq X Y) X
                                         (app (app Gcd (minus X Y)) Y))))))).

trm appnd (fix Appnd\ (abs L1\ (abs L2\
                      (cond (nullp L1) L2
                           (cons (hd L1) (app (app Appnd (tl L1)) L2)))))). 

