(* Ugly tacty to resolve sign condition for N *)
Require Import NAux.
Require Export NGroundTac.
Require Import List.

Open Scope N_scope.


Ltac Nsign_tac :=
  repeat (apply Nmult_le_compat_l || apply Nmult_lt_compat_l ||
          apply Nmult_ge_compat_l || apply Nmult_gt_compat_l ||
          apply Nlt_mult_0 || apply Ngt_mult_0); auto.

Ltac hyp_Nsign_tac H :=
  match type of H with
  | 0 <= _ => clear H
  | (?X1 <= 0)%N => generalize (Nle_0_eq_0 _ H); clear H; intros H; subst X1
  | (?X1 * _ <= ?X1 * _)%N =>
    let s1 := fresh "NS" in
    assert (s1: 0 < X1);
    [ Nsign_tac; fail
    | generalize (Nmult_le_compat_rev_l _ _ _ H s1);
      clear H s1; intros H ]
  | (0 < ?X1 * _)%N =>
    let s1 := fresh "NS" in
    generalize (Nlt_mult_rev_0_l _ _ H);
    generalize (Nlt_mult_rev_0_r _ _ H); clear H;
    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H
  | (?X1 < 0)%N => absurd (~ (X1 < 0)%N); auto
  | (?X1 * _ < ?X1 * _)%N =>
    let s1 := fresh "NS" in
    generalize (Nmult_lt_compat_rev_l1 _ _ _ H);
    generalize (Nmult_lt_compat_rev_l2 _ _ _ H); clear H;
    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H
  | (?X1 >= 0)%N => clear H
  | (0 >= ?X1)%N => generalize (Nge_0_eq_0 _ H); clear H; intros H; subst X1
  | (?X1 * _ >= ?X1 * _)%N =>
    let s1 := fresh "NS" in
    assert (s1: (0 < X1)%N);
    [ Nsign_tac; fail
    | generalize (Nmult_ge_compat_rev_l _ _ _ H s1);
      clear H s1; intros H ]
  | (?X1 * _ > 0 )%N =>
    let s1 := fresh "NS" in
    generalize (Ngt_mult_rev_0_l _ _ H);
    generalize (Ngt_mult_rev_0_r _ _ H); clear H;
    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H
  | (0 > ?X1)%N => absurd (~ (0 > X1)%N); auto with arith
  | (?X1 * _ > ?X1 * _)%N =>
    let s1 := fresh "NS" in
    generalize (Nmult_gt_compat_rev_l1 _ _ _ H);
    generalize (Nmult_gt_compat_rev_l2 _ _ _ H); clear H;
    intros H s1; hyp_Nsign_tac s1; hyp_Nsign_tac H
  | _ =>
    let u := type of H in
    (clear H; assert (H : u); [auto; fail | clear H]) || idtac
  end.

Close Scope N_scope.
