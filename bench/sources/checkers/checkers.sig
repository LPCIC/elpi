sig checkers.

%accum_sig col060.

%accum_sig lists.
%accum_sig base.

type run o.
type resolve (list (pair int form)) -> form -> cert -> o.
type parseInput (list (pair int form)) ->  form -> list int -> form -> list int -> o.
type negateMap (list (pair int form)) -> (list (pair int form)) -> o.
type negateNA form -> form -> o.
type main o.

type bracket          string -> string -> o -> string -> o.  % Auxiliary

% 29 july 2014.
%sig debug.
%accum_sig lists.
type announce o -> o.
type spy string -> o -> o.

type if     o -> o -> o -> o.

/*
Testing
*/
type test int -> A -> B -> o.
                                                                                                    

%sig lists.

type append                     list A -> list A -> list A -> o.
type foreach      (A -> o) -> list A -> o.
type forsome      (A -> o) -> list A -> o.
type memb_and_rest A -> list A -> list A -> o.
type reverse                    list A -> list A -> o.
type member A -> list A -> o.
type foldl (A -> B -> B -> o) -> list A -> B -> B -> o.
type length list A -> int -> o.

type normalize    o -> o.
type rev list A -> list A -> list A -> o.


%sig base.

%accum_sig lists.

kind form, cert type.
kind pair type -> type -> type.
kind map type.

type entry_point  cert -> form -> o.

type map list (pair int form) -> map.
type mapsto int -> form -> o.

type problem  string -> form -> cert -> map -> o.
type resProblem  string -> (list (pair int form)) -> cert -> map -> o.

type all    (A -> form) -> form.
type some   (A -> form) -> form.                                                                                                    
                                                  
%sig col060.

%accum_sig lkf-kernel.

%accum_sig certificatesLKF.

%sig certificatesLKF.
%accum_sig lkf-syntax.
% 29 july 2014.
%sig lkf-syntax.

%accum_sig base.

kind atm, seq, choice, index, direction type.
type unfK list form -> seq.


type left-first, right-first direction.
type inCtxt index -> form -> o.
type left, right choice.
type pr A -> B -> pair A B.

/* Negative Delay */
type d-     form -> form.

/* Positive Delay */
type d+     form -> form.


/* Negative conjunction */
type &-&    form -> form -> form.

/* Positive conjunction */
type &+&    form -> form -> form.

/* Disjunction */
type !-!     form -> form -> form.
type !+!     form -> form -> form.

/* Quantification */
type some   (A -> form) -> form.
type all    (A -> form) -> form.

/* Units */
type f+,f-, t+,t-   form.

infixr &-&, &+& 6.
infixr !-!,!+! 5.


type n, p                 atm -> form.


type unfK list form -> seq.
type foc form -> seq.

type isNegForm, isNegAtm,
     isPosForm, isPosAtm,
     isNeg, isPos, isPosUM    form -> o.
type negateForm form -> form -> o.

type decide_ke          cert -> index -> cert -> o.
type release_ke         cert -> cert -> o.

type store_kc         cert -> form -> index -> cert -> o.
type initial_ke         cert -> index -> o.
type all_kc         cert -> (A -> cert) -> o.
type some_ke          cert -> A -> cert -> o.
type andNeg_kc,  andPos_ke      cert -> form -> cert -> cert -> o.
type andPos_k         cert -> form -> direction -> cert -> cert -> o.
type orNeg_kc           cert -> form -> cert -> o.
type orPos_ke               cert -> form -> choice -> cert -> o.
type true_ke          cert -> o.
type false_kc           cert -> cert -> o.

type cut_ke cert -> form -> cert -> cert -> o.
                                                                                                   

%accum_sig lists.
%accum_sig base.

type check cert -> seq -> o.

type eager_normalize form -> form -> o.


%accum_sig eprover.
%sig eprover.

%accum_sig resolution_steps.

%sig resolution_steps.

%accum_sig certificatesLKF.
%accum_sig lists.
%accum_sig res_base.

%sig res_base.

%accum_sig certificatesLKF.

type idx      int -> index.  % These label clauses which are never literals.
type lit      index. % These label literals that enter the context.
type tlit      index. % index t+

type done cert.
                                                                                              



%accum_sig base.

kind rstep type.
kind resolv type.
kind rclause type.
kind state type. % additional information which might be required by implementing fpcs.

type estate state. %empty state
type istate list int -> state. %state of input formula operands indices

type resolv rclause -> rclause -> int -> resolv.
type rsteps list resolv -> state -> cert. % sequence of steps and a state
type resteps list resolv -> cert. % sequence of steps

type dlist rclause -> rclause -> cert.




%accum_sig binary_res_fol_nosub.

%sig binary_res_fol_nosub.

%accum_sig resolution_steps.
%accum_sig res_base.
%accum_sig lists.
%accum_sig certificatesLKF.

type rid index -> rclause.
type dlist2 rclause -> cert.
type dlist3 cert.

%accum_sig paramodulation.
kind i, arity type.

type ==, =*=    i -> i -> atm.
infix ==, =*= 45.

type inSig  A -> o.

/* Index */
type eqI, reflI, congI, pred4reflI, predI' , predI, symI,lastI index.
type resI, intoI, fromI index.
type chainI int -> index.
/* Certificate */
type c>>, c<< cert -> cert -> cert.
infix c<<, c>> 30.
type witC cert -> cert.
type doneWith, reflC, lastC, useC, decOn index -> cert.
type rewC             index -> int -> cert.
type fromC        index -> cert.
type posResC, posReflC cert.
type pid index -> rclause.
                                                                                  

%accum_sig lists.
%accum_sig certificatesLKF.

% constructor for rclause
type id index -> rclause.

% unary rules
type cn
 rclause -> int -> resolv.

type ignore_rule resolv -> o.
type unary_rule resolv -> int -> int -> o.
type param_rule resolv -> int -> int -> int -> o.

% binary rules
type pm,
     rw
 rclause -> rclause -> int -> resolv.



%accum_sig resolution_steps.
%accum_sig binary_res_fol_nosub.
%accum_sig paramodulation.
%accum_sig base.
%accum_sig lkf-syntax.

type f i -> i.
type g i -> i.
type t i.
type b i.
type apply i -> i -> i.
type h i -> i.


                                                                                                 
                                                                                                    
                                                                                                    
                                                                                                   
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    

