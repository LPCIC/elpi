module helena.

% Helena L: validator for \lambda\delta version 3 ----------------------------

% age: C := user defined

% sort: K := user defined

% Layer: L := user defined

% Global reference R := user defined

% Closed term: T, U, V, W ::= sort   K                   sort of index K
%                          |  abbr   T F where F: T => T abbreviation of T in F
%                          |  abst L T F where F: T => T L-abstraction of type T in F
%                          |  appr   T T                 restricted application
%                          |  appx   T T                 extended application
%                          |  cast   T T                 type annotatiuon
% only for RTM:            |  prod L T F where F: T => T updated L-abstraction of type T in F

% Global environment: G ::= gtop       empty
%                        |  gdef+2 R G pointer to definition of R
%                        |  gdec+2 R G pointer to declaration of R

% application stack: S ::= satom     empty
%                       |  scons S V stacked argument

% RTM mode: M, N := m+0 | m+1 | m+y

% RTM side: E := e+sn | e+dx

% Predicates: m+pred M M         = predeccessor for RTM modes
%             r+exp  T M C E M T = reference expansion
%             rtm+0  T S M M S T = extended reduction  (aux)
%             conv+  T S M M S T = extended conversion (main)
%             conv+l T S M M S T = extended conversion (aux)
%             conv+r T S M M S T = extended conversion (aux)
%             conv+0 T S M M S T = extended conversion (aux)
%             conv+s S S         = extended conversion (aux)

%             ok+l   T M M M T   = ages check
%             appl+  T S M M S T = extended applicability
%             tv+    T           = validity for terms
%             gv+    G           = validity for global environments
%             g+line R C T       = definition/declaration of R

% Parameters: k+succ K K = successor for sort hierarchy
%             l+zero L   = zero layer
%             l+pred L L = predeccessor for layers

% Constants: m+0  = typing not allowed in RTM
%            m+1  = typing required in RTM
%            m+y  = typing allowed in RTM (version 2)
%            e+sn = left side, inferred type
%            e+dx = right side, expected type

% AUXILIARY PREDICATES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

m+pred m+1 m+0.

m+pred m+y m+y.

% EXTENDED REDUCTION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

rtm+0 (appr V T) S M M (scons S V) T.

rtm+0 (appx V T) S M M (scons S V) T.

% beta, epsilon, updated for version 3
rtm+0 (prod L W T) (scons S V) M M S (abbr (cast W V) T).

% e
rtm+0 (cast U T) S m+1 m+0 S U :- !.

% epsilon
rtm+0 (cast U T) S M M S T.

% s
rtm+0 (sort K1) S m+1 m+0 S (sort K2) :- k+succ K1 K2.

% x
rtm+0 (abst L1 W T) S m+1 m+1 S (prod L2 W T) :- !, l+pred L1 L2.

rtm+0 (abst L W T) S M M S (prod L W T).

% EXTENDED CONVERSION PART 1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not in Helena M
% conv+ T S M M S T :- !.

% upsilon, local l
conv+ (prod L W T1) S1 M1 M2 S2 T2 :- l+zero L, !,
                                      pi x\ r+exp x m+1 0 e+sn m+0 W => % m+pred not used
                                            conv+ (T1 x) S1 M1 M2 S2 T2.

% local delta, updated for version 2
conv+ (abbr V T1) S1 M1 M2 S2 T2 :- !,
                                    pi x\ (pi m\ r+exp x m 0 e+sn m V) =>
                                          conv+ (T1 x) S1 M1 M2 S2 T2.

conv+ T1 S1 M1 M2 S2 T2 :- rtm+0 T1 S1 M1 M S T, !, conv+ T S M M2 S2 T2.

conv+ T1 S1 M1 M2 S2 T2 :- conv+r T2 S2 M2 M1 S1 T1.

% EXTENDED CONVERSION PART 2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not in Helena M
% conv+l T S M M S T :- !.

% upsilon, local l
conv+l (prod L W T1) S1 M1 M2 S2 T2 :- l+zero L, !,
                                       pi x\ r+exp x m+1 0 e+sn m+0 W => % m+pred not used
                                             conv+l (T1 x) S1 M1 M2 S2 T2.

% local delta, updated for version 2
conv+l (abbr V T1) S1 M1 M2 S2 T2 :- !,
                                     pi x\ (pi m\ r+exp x m 0 e+sn m V) =>
                                           conv+l (T1 x) S1 M1 M2 S2 T2.

conv+l T1 S1 M1 M2 S2 T2 :- rtm+0 T1 S1 M1 M S T, !, conv+l T S M M2 S2 T2.

conv+l T1 S1 M1 M2 S2 T2 :- conv+0 T1 S1 M1 M2 S2 T2.

% EXTENDED CONVERSION PART 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not in Helena M
% conv+r T S M M S T :- !.

% upsilon, local l
conv+r (prod L W T1) S1 M1 M2 S2 T2 :- l+zero L, !,
                                       pi x\ r+exp x m+1 0 e+dx m+0 W => % m+pred not used
                                             conv+r (T1 x) S1 M1 M2 S2 T2.

% local delta, updated for version 2
conv+r (abbr V T1) S1 M1 M2 S2 T2 :- !,
                                     pi x\ (pi m\ r+exp x m 0 e+dx m V) =>
                                           conv+r (T1 x) S1 M1 M2 S2 T2.

conv+r T1 S1 M1 M2 S2 T2 :- rtm+0 T1 S1 M1 M S T, !, conv+r T S M M2 S2 T2.

conv+r T1 S1 M1 M2 S2 T2 :- conv+0 T2 S2 M2 M1 S1 T1.

% EXTENDED CONVERSION PART 4 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

conv+s satom satom.

conv+s (scons S1 V1) (scons S2 V2) :- conv+s S1 S2,
                                      conv+ V1 satom m+0 m+0 satom V2.

% not in Helena M
% conv+0 T S M M S T :- !.

% local l, updated for version 2 and 3
conv+0 (prod L W1 T1) satom M1 M2 satom (prod L W2 T2) :- !,
                                                          conv+ W1 satom m+0 m+0 satom W2,
                                                          pi x\ (r+exp x m+1 0 e+sn m+0 W1 :- !) => % m+pred not used
                                                                (r+exp x m+1 0 e+dx m+0 W2)      => % m+pred not used
                                                                conv+ (T1 x) satom M1 M2 satom (T2 x).

conv+0 T S1 M M S2 T :- conv+s S1 S2, !.

% left expansion
conv+0 T1 S1 M1 M2 S2 T2 :- r+exp T1 M1 C1 e+sn M T, ok+l C1 M1 M M2 T2, !, conv+l T S1 M M2 S2 T2.

% right expansion
conv+0 T1 S1 M1 M2 S2 T2 :- r+exp T2 M2 C2 e+dx M T, conv+r T S2 M M1 S1 T1.

ok+l C1 m+1 m+0 M2 T2 :- !.

ok+l C1 M1 M M2 T2 :- r+exp T2 M2 C2 e+dx N U, !, C2 > C1.

ok+l C1 M1 M M2 T2.

% EXTENDED APPLICABILITY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% upsilon forbidden for applicability

% local delta, updated for version 2
appl+ (abbr V T1) S M T2 :- !,
                             pi x\ (pi m\ r+exp x m 0 e+dx m V) =>
                                   appl+ (T1 x) S M T2.

appl+ (prod L W U) satom M V :- !, conv+ V satom m+1 m+0 satom W.

appl+ T1 S1 M1 T2 :- rtm+0 T1 S1 M1 M S T, !, appl+ T S M T2.

% right expansion
appl+ T1 S M1 T2 :- r+exp T1 M1 C1 e+dx M2 T, !, appl+ T S M2 T2.

% VALIDITY FOR TERMS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tv+ (sort N).

% local delta updated for version 2
tv+ (abbr V T) :- tv+ V,
                  pi x\ tv+ x =>
                        (pi m\ pi e\ r+exp x m 0 e m V) =>
                        tv+ (T x).

% local l updated for version 2 and 3
tv+ (abst L W T) :- tv+ W,
                    pi x\ tv+ x =>
                          (pi m1\ pi m2\ pi e\ r+exp x m1 0 e m2 W :- m+pred m1 m2) =>
                          tv+ (T x).

% restricted applicability condition (version 1) updated for version 3
tv+ (appr V T) :- tv+ V, tv+ T, appl+ T satom m+1 V.

%extended applicability condition (version 2) updated for version 3
tv+ (appx V T) :- tv+ V, tv+ T, appl+ T satom m+y V.

tv+ (cast U T) :- tv+ U, tv+ T, conv+ T satom m+1 m+0 satom U.

% VALIDITY FOR GLOBAL ENVIRONMENTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gv+ gtop.

gv+ (genv C) :- g+list C G, gv+ G.

% global delta updated for version 2
gv+ (gdef+1 C V G) :- tv+ V,
                      pi x\ tv+ x =>
                            (pi m\ pi e\ r+exp x m C e m V) =>
                            gv+ (G x).

% global l updated for version 2
gv+ (gdec+1 C W G) :- tv+ W,
                      pi x\ tv+ x =>
                            (pi m1\ pi m2\ pi e\ r+exp x m1 C e m2 W :- m+pred m1 m2) =>
                            gv+ (G x).

% global delta updated for version 2
gv+ (gdef+2 R G) :- g+line R C V,
                    printterm std_out R, print "\n",
                    tv+ V,
%                    tv+c C V,
                    (tv+ R => (pi m\ pi e\ r+exp R m C e m V) => gv+ G).

% global l updated for version 2
gv+ (gdec+2 R G) :- g+line R C W,
                    printterm std_out R, print "\n",
                    tv+ W,
%                    tv+c C W,
                    (tv+ R => (pi m1\ pi m2\ pi e\ r+exp R m1 C e m2 W :- m+pred m1 m2) => gv+ G).

gv+3 R :- g+line R C T,
%          printterm std_out T, print "\n",
          tv+ T.

% Additions ------------------------------------------------------------------

% LAYERS FOR PTS, LAMBDA-INFINITY, AUT-68, AUT-QE %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Constants: l+0 = hyper Pi
%            l+1 = Pi
%            l+2 = lambda
%            l+y = lambda-infinity

l+zero l+0.

l+pred l+0 l+0.

l+pred l+1 l+0.

l+pred l+2 l+1.

l+pred l+y l+y.
