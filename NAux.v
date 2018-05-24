Require Export NArith.
Require Import ZArith.

Open Scope N_scope.


Theorem N_nat_correct: forall n, nat_of_N (N_of_nat n) = n.
intros n; case n; simpl; auto.
exact nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Theorem nat_N_correct: forall n, N_of_nat (nat_of_N n) = n.
intros n; case n; simpl; auto.
intros; elim p using Pind; simpl; auto.
intros n1 H; rewrite nat_of_P_succ_morphism; simpl.
apply f_equal with (f:= Npos); apply P_of_succ_nat_o_nat_of_P_eq_succ.
Qed.

Theorem Nle_le: forall n  m, (nat_of_N n <= nat_of_N m)%nat -> n <= m.
intros n m; case n; case m; unfold N.le; simpl; try (intros; discriminate).
intros p; elim p using Pind; simpl.
intros H1; inversion H1. 
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 > nat_of_P p1)%nat; auto with arith.
apply nat_of_P_gt_Gt_compare_morphism; auto.
Qed.

Theorem le_Nle: forall n m, N_of_nat n <= N_of_nat m -> (n <= m)%nat.
intros n m; case n; case m; unfold N.le; simpl; auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1; case (le_or_lt n1 m1); auto with arith.
intros H2; case H1.
apply nat_of_P_gt_Gt_compare_complement_morphism.
repeat rewrite  nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.

Theorem Nle_le_rev: forall n  m, n <= m -> (nat_of_N n <= nat_of_N m)%nat.
intros; apply le_Nle; repeat rewrite nat_N_correct; auto.
Qed.

Theorem Nlt_lt: forall n  m, (nat_of_N n < nat_of_N m)%nat -> n < m.
intros n m; case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
intros; apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
Qed.

Theorem lt_Nlt: forall n m, N_of_nat n < N_of_nat m -> (n < m)%nat.
intros n m; case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (N_nat_correct (S n1)); rewrite <- (N_nat_correct (S m1)).
simpl; apply nat_of_P_lt_Lt_compare_morphism; auto.
Qed.

Theorem Nlt_lt_rev: forall n  m, n < m -> (nat_of_N n < nat_of_N m)%nat.
intros; apply lt_Nlt; repeat rewrite nat_N_correct; auto.
Qed.


Theorem Nge_ge: forall n  m, (nat_of_N n >= nat_of_N m)%nat -> n >= m.
intros n m; case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto.
intros p; elim p using Pind; simpl.
intros H1; inversion H1. 
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 < nat_of_P p1)%nat; auto with arith.
apply nat_of_P_lt_Lt_compare_morphism; auto.
Qed.

Theorem ge_Nge: forall n m, N_of_nat n >= N_of_nat m -> (n >= m)%nat.
intros n m; case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1.
case (le_or_lt m1 n1); auto with arith.
intros H2; case H1.
apply nat_of_P_lt_Lt_compare_complement_morphism.
repeat rewrite  nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.

Theorem Nge_ge_rev: forall n  m, n >= m -> (nat_of_N n >= nat_of_N m)%nat.
intros; apply ge_Nge; repeat rewrite nat_N_correct; auto.
Qed.


Theorem Ngt_gt: forall n  m, (nat_of_N n > nat_of_N m)%nat -> n > m.
intros n m; case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
intros; apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
Qed.

Theorem gt_Ngt: forall n m, N_of_nat n > N_of_nat m -> (n > m)%nat.
intros n m; case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (N_nat_correct (S n1)); rewrite <- (N_nat_correct (S m1)).
simpl; apply nat_of_P_gt_Gt_compare_morphism; auto.
Qed.

Theorem Ngt_gt_rev: forall n  m, n > m -> (nat_of_N n > nat_of_N m)%nat.
intros; apply gt_Ngt; repeat rewrite nat_N_correct; auto.
Qed.

Theorem Neq_eq: forall n  m, (nat_of_N n = nat_of_N m)%nat -> n = m.
intros n m H; rewrite <- (nat_N_correct n); rewrite <- (nat_N_correct m).
apply f_equal with (f := N_of_nat); auto.
Qed.

Theorem eq_Neq: forall n m, N_of_nat n = N_of_nat m -> n = m.
intros n m H; rewrite <- (N_nat_correct n); rewrite <- (N_nat_correct m).
apply f_equal with (f := nat_of_N); auto.
Qed.

Theorem Neq_eq_rev: forall n  m, n = m -> (nat_of_N n = nat_of_N m)%nat.
intros; apply eq_Neq; repeat rewrite nat_N_correct; auto.
Qed.

Import BinPos.

Theorem Nplus_plus: forall x y, nat_of_N (x + y) = (nat_of_N x + nat_of_N y)%nat.
intros x y; case x; case y; unfold Nplus; simpl; auto.
intros p1 p2; rewrite <- nat_of_P_plus_morphism; auto.
Qed.

Theorem plus_Nplus: forall x y, N_of_nat (x + y) =  N_of_nat x + N_of_nat y.
intros x y; rewrite <- (nat_N_correct (N_of_nat x + N_of_nat y)).
rewrite Nplus_plus; repeat rewrite N_nat_correct; auto.
Qed.

Theorem Nmult_mult: forall x y, nat_of_N (x * y) = (nat_of_N x * nat_of_N y)%nat.
intros x y; case x; case y; unfold Nmult; simpl; auto.
intros p1 p2; rewrite <- nat_of_P_mult_morphism; auto.
Qed.

Theorem mult_Nmult: forall x y, N_of_nat (x * y) = N_of_nat x * N_of_nat y.
intros x y; rewrite <- (nat_N_correct (N_of_nat x * N_of_nat y)).
rewrite Nmult_mult; repeat rewrite N_nat_correct; auto.
Qed.

Ltac to_nat_op  :=
  match goal with
      H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H
|     H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H
|     H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H
|     H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H
|     H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H
|      |- (N.lt _ _)  => apply Nlt_lt
|      |- (N.le _ _)  => apply Nle_le
|      |- (N.gt _ _)  => apply Ngt_gt
|      |- (N.ge _ _)  => apply Nge_ge
|      |- (@eq N _ _)  => apply Neq_eq
end.

Ltac set_to_nat :=
let nn := fresh "nn" in
match goal with
       |- context [(nat_of_N (?X + ?Y)%N)]  => rewrite Nplus_plus
|      |- context [(nat_of_N (?X * ?Y)%N)]  => rewrite Nmult_mult
|      |- context [(nat_of_N ?X)]  => set (nn:=nat_of_N X) in * |- *
|      H: context [(nat_of_N (?X + ?Y)%N)] |- _ => rewrite Nplus_plus in H
|      H: context [(nat_of_N (?X + ?Y)%N)] |- _ => rewrite Nmult_mult in H
|      H: context [(nat_of_N ?X)] |- _ => set (nn:=nat_of_N X) in * |- *
end.

Ltac to_nat := repeat to_nat_op; repeat set_to_nat.

Theorem Nle_refl : forall x, x <= x.
intros; to_nat; auto with arith.
Qed.

Theorem Nle_trans : forall x y z, x <= y -> y <= z -> x <= z.
intros; to_nat; apply le_trans with nn1; auto.
Qed.

Theorem Nle_gt_trans: forall n m p, m <= n -> m > p -> n > p.
intros; to_nat; apply le_gt_trans with nn1; auto.
Qed.

Theorem Nle_lt_trans: forall n m p, n <= m -> m < p -> n < p.
intros; to_nat; apply le_lt_trans with nn1; auto.
Qed.

Theorem Ngt_le_trans: forall n m p, n > m -> p <= m -> n > p.
intros; to_nat; apply gt_le_trans with nn1; auto.
Qed.

Theorem Nlt_le_trans: forall n m p, n < m -> m <= p -> n < p.
intros; to_nat; apply lt_le_trans with nn1; auto.
Qed.

Theorem Nle_plus_compat : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
intros; to_nat; apply plus_le_compat; auto.
Qed.

Theorem Nle_0_plus_compat :
  forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
intros; to_nat; auto with arith.
Qed.

Theorem Nle_plus_r :
  forall x y, x <= x + y.
intros; to_nat; auto with arith.
Qed.

Theorem Nle_plus_l :
  forall x y, x <= y + x.
intros; to_nat; auto with arith.
Qed.

Close Scope N_scope.
