/*
 * Encodings of some formulas in the object logic considered
 */

module formulas.

accum_sig  logic, nonlogical.

kind	xname		type.

type	formula		xname -> bool -> o.

formula bugs
 (((heated jar) && (forall X\ ((bug X) ==> (animal X))) &&
   (forall X\ (forall Y\ (((heated Y) && ((in X Y) && (animal X)))
                            ==> (dead X)))) &&
   (forall Y\ ((forall X\ (((in X Y) && (bug X)) ==> (dead X)))
    ==> (sterile Y))))
  ==> (sterile jar)).


formula baffler (some X\ (forall Y\ ((p X) ==> (p Y)))).

formula cases1 (((q a) || (q b)) ==> (some X\ (q X))).

