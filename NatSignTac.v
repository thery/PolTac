(* Ugly tacty to resolve sign condition for nat *)
Require Import NatAux.
Require Export NatGroundTac.

Ltac nsign_tac :=
  repeat (apply Nat.mul_le_mono_l || apply mult_lt_compat_l ||
          apply mult_ge_compat_l || apply mult_gt_compat_l ||
          apply lt_mult_0 || apply gt_mult_0); auto with arith.

Ltac hyp_nsign_tac H :=
  match type of H with
  | 0 <= _ => clear H
  | ?X1 <= 0 => generalize (le_0_eq_0 _ H); clear H; intros H; subst X1
  | ?X1 * _ <= ?X1 * _ =>
    let s1 := fresh "NS" in
    assert (s1: 0 < X1);
    [ nsign_tac; fail
    | generalize (mult_le_compat_rev_l _ _ _ H s1);
      clear H s1; intros H ]
  |  0 < ?X1 * _ =>
     let s1 := fresh "NS" in
     generalize (lt_mult_rev_0_l _ _ H);
     generalize (lt_mult_rev_0_r _ _ H); clear H;
     intros H s1; hyp_nsign_tac s1; hyp_nsign_tac H
  | ?X1 < 0 => absurd (~ (X1 < 0)); auto with arith
  | ?X1 * _ < ?X1 * _ =>
    let s1 := fresh "NS" in
    generalize (mult_lt_compat_rev_l1 _ _ _ H);
    generalize (mult_lt_compat_rev_l2 _ _ _ H); clear H;
    intros H s1; hyp_nsign_tac s1; hyp_nsign_tac H
  | ?X1 >= 0 => clear H
  | 0 >= ?X1 => generalize (le_0_eq_0 _ H); clear H; intros H; subst X1
  | ?X1 * _ >= ?X1 * _ =>
    let s1 := fresh "NS" in
    assert (s1: 0 < X1);
    [ nsign_tac; fail
    | generalize (mult_ge_compat_rev_l _ _ _ H s1);
      clear H s1; intros H ]
  | ?X1 * _ > 0 =>
    let s1 := fresh "NS" in
    generalize (gt_mult_rev_0_l _ _ H);
    generalize (gt_mult_rev_0_r _ _ H); clear H;
    intros H s1; hyp_nsign_tac s1; hyp_nsign_tac H
  | 0 > ?X1 => absurd (~ (0 > X1)); auto with arith
  | ?X1 * _ > ?X1 * _ =>
    let s1 := fresh "NS" in
    generalize (mult_gt_compat_rev_l1 _ _ _ H);
    generalize (mult_gt_compat_rev_l2 _ _ _ H); clear H;
    intros H s1; hyp_nsign_tac s1; hyp_nsign_tac H
  | _ =>
    let u := type of H in
    (clear H; assert (H : u); [auto with arith; fail | clear H]) || idtac
  end.

(* Test *)
Section Test.

Let hyp_test a b c d e :
  0 <= a -> 0 < a -> a * b <= a * c -> b * a <= b * c -> 
  d <= 0 -> e < 0 -> d = 0.
Proof.
intros H H1 H2 H3 H4 H5.
(* H should disappear *)
hyp_nsign_tac H.
(* a in H2 should disappear *)
hyp_nsign_tac H2.
(* H3 unchanged *)
try hyp_nsign_tac H3.
(* d should disappear *)
hyp_nsign_tac H4.
(* Prove it *)
hyp_nsign_tac H5.
Qed.

Let hyp_test1 a b c d e :
  a >= 0 -> a > 0 -> a * b > a * c -> b * a >= b * c -> 0 >= d -> 0 > e -> 
  d = 0.
Proof.
intros H H1 H2 H3 H4 H5.
(* H should disappear *)
hyp_nsign_tac H.
(* a in H2 should disappear *)
hyp_nsign_tac H2.
(* H3 unchanged *)
try hyp_nsign_tac H3.
(* d should disappear *)
hyp_nsign_tac H4.
(* Prove it *)
hyp_nsign_tac H5.
Qed.

End Test.
