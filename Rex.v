Require Import Reals.
Require Import PolTac.

Open Scope R_scope.

Theorem pols_test1 x y :
  x < y -> x + x < y + x.
Proof.
intros.
pols.
auto.
Qed.

Theorem pols_test2 x y :
  0 < y -> x < x + y.
Proof.
intros.
pols.
auto.
Qed.

Theorem pols_test3 x y :
  0 < y * y ->
  (x + y) * (x - y) < x * x.
Proof.
intros.
pols.
auto with real.
Qed.

Theorem pols_test4 x y :
  x * x < y * y ->
  (x + y) * (x + y) < 2 * (x * y + y * y).
Proof.
intros.
pols.
auto.
Qed.

Theorem pols_test5 x y z :
  x * (z + 2) < y * (2 * x + 1) ->
  x * (z + y + 2) < y * (3 * x + 1).
Proof.
intros.
pols.
auto.
Qed.

Theorem polf_test1 x y :
  0 <= x -> 1 <= y -> x <= x * y.
Proof.
intros.
polf.
Qed.

Theorem polf_test2 x y :
  0 < x -> x <= x * y -> 1 <= y.
Proof.
intros H1 H2.
hyp_polf H2.
Qed.

Theorem polr_test1 x y z :
  x + z < y ->
  x + y + z < 2 * y.
Proof.
intros H.
polr H.
pols.
auto.
pols.
auto with real.
Qed.

Theorem polr_test2 x y z t u :
  t < 0 -> y = u ->
  x + z < y ->
  2 * y * t < x * t + t * u + z * t.
Proof.
intros H1 H2 H3.
polf.
polr H2; auto with real.
polr H3.
pols.
auto.
pols.
auto with real.
Qed.
