From Stdlib Require Export NArith.
From Stdlib Require Import ZArith.
Require Import NatAux.

Open Scope N_scope.

Theorem Nle_le n m : (N.to_nat n <= N.to_nat m)%nat -> n <= m.
Proof.
case n; case m; unfold N.le; simpl; try (intros; discriminate).
intros p; elim p using Pind; simpl.
intros H1; inversion H1.
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 > nat_of_P p1)%nat; auto with arith.
apply nat_of_P_gt_Gt_compare_morphism; auto.
Qed.

Theorem le_Nle n m : N.of_nat n <= N.of_nat m -> (n <= m)%nat.
Proof.
case n; case m; unfold N.le; simpl; auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1; case (Nat.le_gt_cases n1 m1); auto with arith.
intros H2; case H1.
apply nat_of_P_gt_Gt_compare_complement_morphism.
repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.

Theorem Nle_le_rev n m : n <= m -> (N.to_nat n <= N.to_nat m)%nat.
Proof. intros; apply le_Nle; repeat rewrite N2Nat.id; auto. Qed.

Theorem Nlt_lt n m : (N.to_nat n < N.to_nat m)%nat -> n < m.
Proof.
case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
intros; apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
Qed.

Theorem lt_Nlt n m : N.of_nat n < N.of_nat m -> (n < m)%nat.
Proof.
case n; case m; unfold N.lt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (Nat2N.id (S n1)); rewrite <- (Nat2N.id (S m1)).
simpl; apply nat_of_P_lt_Lt_compare_morphism; auto.
Qed.

Theorem Nlt_lt_rev n m : n < m -> (N.to_nat n < N.to_nat m)%nat.
Proof. intros; apply lt_Nlt; repeat rewrite N2Nat.id; auto. Qed.


Theorem Nge_ge n m : (N.to_nat n >= N.to_nat m)%nat -> n >= m.
Proof.
case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto.
intros p; elim p using Pind; simpl.
intros H1; inversion H1.
intros n1 _; rewrite nat_of_P_succ_morphism.
intros H1; inversion H1.
intros p1 p2 H1 H2; absurd (nat_of_P p2 < nat_of_P p1)%nat; auto with arith.
apply nat_of_P_lt_Lt_compare_morphism; auto.
Qed.

Theorem ge_Nge n m : N.of_nat n >= N.of_nat m -> (n >= m)%nat.
Proof.
case n; case m; unfold N.ge; simpl; try (intros; discriminate); auto with arith.
intros n1 H1; case H1; auto.
intros m1 n1 H1.
case (Nat.le_gt_cases m1 n1); auto with arith.
intros H2; case H1.
apply nat_of_P_lt_Lt_compare_complement_morphism.
repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.

Theorem Nge_ge_rev n m : n >= m -> (N.to_nat n >= N.to_nat m)%nat.
Proof. intros; apply ge_Nge; repeat rewrite N2Nat.id; auto. Qed.

Theorem Ngt_gt n m : (N.to_nat n > N.to_nat m)%nat -> n > m.
Proof.
case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto.
intros H1; inversion H1.
intros p H1; inversion H1.
intros; apply nat_of_P_gt_Gt_compare_complement_morphism; auto.
Qed.

Theorem gt_Ngt n m : N.of_nat n > N.of_nat m -> (n > m)%nat.
Proof.
case n; case m; unfold N.gt; simpl; try (intros; discriminate); auto with arith.
intros m1 n1 H1.
rewrite <- (Nat2N.id (S n1)); rewrite <- (Nat2N.id (S m1)).
simpl; apply nat_of_P_gt_Gt_compare_morphism; auto.
Qed.

Theorem Ngt_gt_rev n m : n > m -> (N.to_nat n > N.to_nat m)%nat.
Proof. intros; apply gt_Ngt; repeat rewrite N2Nat.id; auto. Qed.

Theorem Neq_eq_rev n m : n = m -> (N.to_nat n = N.to_nat m)%nat.
Proof. intros H; rewrite H; auto. Qed.

Theorem Nmult_lt_compat_l n m p : n < m -> 0 < p -> p * n < p * m.
Proof.
intros H1 H2; apply Nlt_lt; repeat rewrite N2Nat.inj_mul.
apply mult_lt_compat_l; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_le_compat_l n m p : n <= m -> p * n <= p * m.
Proof.
intros H1; apply Nle_le; repeat rewrite N2Nat.inj_mul.
apply Nat.mul_le_mono_l; apply le_Nle; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_ge_compat_l n m p : n >= m -> p * n >= p * m.
Proof.
intros H1; apply Nge_ge; repeat rewrite N2Nat.inj_mul.
apply mult_ge_compat_l; apply ge_Nge; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_l n m p : n > m -> p > 0 -> p * n > p * m.
Proof.
intros H1 H2; apply Ngt_gt; repeat rewrite N2Nat.inj_mul.
apply mult_gt_compat_l; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_lt_compat_rev_l1 n m p : p * n < p * m -> 0 < p.
Proof.
intros H1; apply Nlt_lt.
apply mult_lt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
repeat rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_lt_compat_rev_l2 n m p : p * n < p * m -> n < m.
Proof.
intros H1; apply Nlt_lt; apply mult_lt_compat_rev_l2 with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_rev_l1 n m p : p * n > p * m -> p > 0.
Proof.
intros H1; apply Ngt_gt.
apply mult_gt_compat_rev_l1 with (nat_of_N n) (nat_of_N m).
repeat rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_gt_compat_rev_l2 n m p : p * n > p * m -> n > m.
Proof.
intros H1; apply Ngt_gt; apply mult_gt_compat_rev_l2 with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_le_compat_rev_l n m p : p * n <= p * m -> 0 < p -> n <= m.
Proof.
intros H1 H2; apply Nle_le; apply mult_le_compat_rev_l with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply le_Nle; repeat rewrite N2Nat.id; auto.
apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nmult_ge_compat_rev_l n m p : p * n >= p * m -> 0 < p -> n >= m.
Proof.
intros H1 H2; apply Nge_ge; apply mult_ge_compat_rev_l with (nat_of_N p).
repeat rewrite <- N2Nat.inj_mul; apply ge_Nge; repeat rewrite N2Nat.id; auto.
apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_0 a b : 0 < a -> 0 < b -> 0 < a * b.
Proof.
intros H1 H2; apply Nlt_lt; rewrite N2Nat.inj_mul; apply lt_mult_0;
  apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_0 a b : a > 0 -> b > 0 -> a * b > 0.
Proof.
intros H1 H2; apply Ngt_gt; rewrite N2Nat.inj_mul; apply gt_mult_0;
    apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_rev_0_l a b : 0 < a * b -> 0 < a .
Proof.
intros H1; apply Nlt_lt; apply lt_mult_rev_0_l with (nat_of_N b).
rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nlt_mult_rev_0_r a b : 0 < a * b -> 0 < b .
Proof.
intros H1; apply Nlt_lt; apply lt_mult_rev_0_r with (nat_of_N a).
rewrite <- N2Nat.inj_mul; apply lt_Nlt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_rev_0_l a b : a * b > 0 -> a > 0.
Proof.
intros H1; apply Ngt_gt; apply gt_mult_rev_0_l with (nat_of_N b).
rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Ngt_mult_rev_0_r a b : a * b > 0 -> b > 0 .
Proof.
intros H1; apply Ngt_gt; apply gt_mult_rev_0_r with (nat_of_N a).
rewrite <- N2Nat.inj_mul; apply gt_Ngt; repeat rewrite N2Nat.id; auto.
Qed.

Theorem Nle_0_eq_0 n : n <= 0 -> n = 0.
Proof.
intros H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
apply le_Nle; rewrite N2Nat.id; auto.
Qed.

Theorem Nge_0_eq_0 n : 0 >= n -> n = 0.
Proof.
intros H1; rewrite <- (N2Nat.id n).
rewrite (le_0_eq_0 (nat_of_N n)); auto.
change (0 >= nat_of_N n)%nat.
apply ge_Nge; rewrite N2Nat.id; auto.
Qed.

Import BinPos.

Ltac to_nat_op :=
  match goal with
  | H: (N.lt _ _) |- _ => generalize (Nlt_lt_rev _ _ H); clear H; intros H
  | H: (N.gt _ _) |- _ => generalize (Ngt_gt_rev _ _ H); clear H; intros H
  | H: (N.le _ _) |- _ => generalize (Nle_le_rev _ _ H); clear H; intros H
  | H: (N.ge _ _) |- _ => generalize (Nge_ge_rev _ _ H); clear H; intros H
  | H: (@eq N _ _) |- _ => generalize (Neq_eq_rev _ _ H); clear H; intros H
  | |- (N.lt _ _) => apply Nlt_lt
  | |- (N.le _ _) => apply Nle_le
  | |- (N.gt _ _) => apply Ngt_gt
  | |- (N.ge _ _) => apply Nge_ge
  | |- (@eq N _ _) => apply Nat2N.inj
  end.

Ltac set_to_nat :=
  let nn := fresh "nn" in
  match goal with
  | |- context [(N.to_nat (?X + ?Y)%N)] => rewrite N2Nat.inj_add
  | |- context [(N.to_nat (?X * ?Y)%N)] => rewrite N2Nat.inj_mul
  | |- context [(N.to_nat ?X)] => set (nn:=N.to_nat X) in * |- *
  | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_add in H
  | H: context [(N.to_nat (?X + ?Y)%N)] |- _ => rewrite N2Nat.inj_mul in H
  | H: context [(N.to_nat ?X)] |- _ => set (nn:=N.to_nat X) in * |- *
  end.

Ltac to_nat := repeat to_nat_op; repeat set_to_nat.

Theorem Nle_gt_trans n m p : m <= n -> m > p -> n > p.
Proof. intros; to_nat; apply Nat.lt_le_trans with nn1; auto. Qed.

Theorem Ngt_le_trans n m p : n > m -> p <= m -> n > p.
Proof. intros; to_nat; apply Nat.le_lt_trans with nn1; auto. Qed.

Theorem Nle_add_l x y : x <= y + x.
Proof. intros; to_nat; auto with arith. Qed.

Close Scope N_scope.
