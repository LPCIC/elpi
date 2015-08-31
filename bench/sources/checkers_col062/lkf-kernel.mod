% 29 july 2014.
module lkf-kernel.
accumulate lists.

% Entry point
entry_point Cert Form :-
  check Cert (unfK [Form]).

%%%%%%%%%%%%%%%%%%
% Structural Rules
%%%%%%%%%%%%%%%%%%

% decide
check Cert (unfK nil) :-
  decide_ke Cert Indx Cert',
  inCtxt Indx P,
  isPos P,
  check Cert' (foc P).
% release
check Cert (foc N) :-
  isNeg N,
  release_ke Cert Cert',
  check Cert' (unfK [N]).
% store
check Cert (unfK [C|Rest]) :-
  (isPos C ; isNegAtm C),
  store_kc Cert C Indx Cert',
  inCtxt Indx C => check Cert' (unfK Rest).
% initial
check Cert (foc (p A)) :-
  initial_ke Cert Indx,
  inCtxt Indx (n A).
% cut
check Cert (unfK nil) :-
  cut_ke Cert F CertA CertB,
  negateForm F NF,
  check CertA (unfK [F]),
  check CertB (unfK [NF]).

%%%%%%%%%%%%%%%%%%%%
% Asynchronous Rules
%%%%%%%%%%%%%%%%%%%%

% orNeg
check Cert (unfK [A !-! B | Rest]) :-
  orNeg_kc Cert (A !-! B)  Cert',
  check Cert' (unfK [A, B| Rest]).
% conjunction
check Cert (unfK [A &-& B | Rest]) :-
  andNeg_kc Cert (A &-& B) CertA CertB,
  check CertA (unfK [A | Rest]),
  check CertB (unfK [B | Rest]).
% forall
check Cert (unfK [all B | Theta]) :-
  all_kc Cert Cert',
  pi w\ normalize (check (Cert' w) (unfK [B w | Theta] )).
% Units
check Cert (unfK [t-|_]). % No clerk - justify in the paper ?
check Cert (unfK [f-|Gamma]) :-  % Fix the name, between Theta, Teta, Gamma !
  false_kc Cert Cert',
  check Cert' (unfK Gamma).
% delay
check Cert (unfK [d- A| Teta]) :-
  check Cert (unfK [A| Teta]).

%%%%%%%%%%%%%%%%%%%
% Synchronous Rules
%%%%%%%%%%%%%%%%%%%
% conjunction
check Cert (foc (A &+& B)) :-
   andPos_k Cert (A &+& B) Direction CertA CertB,
   ((Direction = left-first,
   check CertA (foc A),
   check CertB (foc B));
   (Direction = right-first,
    check CertB (foc B),check CertA (foc A))).
% disjunction
check Cert (foc (A !+! B)) :-
  orPos_ke Cert (A !+! B) Choice Cert',
  ((Choice = left,  check Cert' (foc A));
   (Choice = right, check Cert' (foc B))).
% quantifers
check Cert (foc (some B)) :-
  some_ke Cert T Cert',
  eager_normalize (B T) C, % required as Teyjus doesnt normalize it before pattern matching.
  check Cert' (foc (C)).
% Units
check Cert (foc t+) :-
  true_ke Cert.
% delay
check Cert (foc (d+ A)) :-
  check Cert (foc A).

%%%%%%%%%%%
% Utilities
%%%%%%%%%%%

eager_normalize A B :- A = B.

isNegForm (_ &-& _).
isNegForm (_ !-! _).
isNegForm (d- _).
isNegForm (all _).
isPosForm (_ &+& _).
isPosForm (d+ _).
isPosForm (_ !+!  _).
isNegAtm (n _).
isPosAtm (p _).
isPosForm (some _).
isPosForm t+.
isPosForm f+.
isNegForm f-.
isNegForm t-.
isNeg A :- isNegForm A ; isNegAtm A.
isPos A :- isPosForm A ; isPosAtm A.
isPosUM A :- isPos A ; isNegAtm A.

negateForm f- t+.
negateForm t+ f-.
negateForm t- f+.
negateForm f+ t-.

negateForm (p A) (n A).
negateForm (n A) (p A).
negateForm (A &+& B)  (NA !-! NB) &
negateForm (A !-! B)  (NA &+& NB) &
negateForm (A &-& B)  (NA !+! NB) &
negateForm (A !+! B)  (NA &-& NB) :- negateForm A NA, negateForm B NB.
negateForm (all B)  (some NB) &
negateForm (some B) (all NB) :- pi x\ negateForm (B x) (NB x).


/* Temporary : for backwards compatibility.
Once the andPos_ke has been changed everywhere, andPos_k can be changed to andPos_ke,
for now andPos_k calls on andPos_ke.
*/

andPos_k Cert (A &+& B) left-first CertA CertB :-
   andPos_ke Cert (A &+& B) CertA CertB.
