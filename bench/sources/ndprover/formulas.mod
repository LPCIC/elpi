/*
 * Encodings of some formulas in the object logic considered
 */

module formulas.

accum_sig  logic, nonlogical.

kind	name		type.

type	formula		name -> bool -> o.

formula bugs
 (((heated jar) and (forall X\ ((bug X) imp (animal X))) and
   (forall X\ (forall Y\ (((heated Y) and (in X Y) and (animal X))
                            imp (dead X)))) and
   (forall Y\ ((forall X\ (((in X Y) and (bug X)) imp (dead X)))
    imp (sterile Y))))
  imp (sterile jar)).


formula baffler (some X\ (forall Y\ ((p X) imp (p Y)))).

formula cases1 (((q a) or (q b)) imp (some X\ (q X))).

