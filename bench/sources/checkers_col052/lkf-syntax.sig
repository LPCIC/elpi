% 29 july 2014.
sig lkf-syntax.

accum_sig base.

kind atm, seq, choice, index, direction type.

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
type f+,f-, t+,t- 	form.

infixr &-&, &+& 136.
infixr !-!,!+! 135.


type n, p      	       	  atm -> form.


type unfK list form -> seq.
type foc form -> seq.
type isNegForm, isNegAtm,
     isPosForm, isPosAtm,
     isNeg, isPos, isPosUM	  form -> o.
type negateForm form -> form -> o.
