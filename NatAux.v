Require Export Arith.

Theorem mult_lt_compat_l n m p : n < m -> 0 < p -> p * n < p * m.
Proof.
intros H H1; repeat rewrite (Nat.mul_comm p); apply Nat.mul_lt_mono_pos_r; auto.
Qed.

Theorem mult_ge_compat_l n m p : n >= m -> p * n >= p * m.
Proof. intros H; auto with arith. Qed.

Theorem mult_gt_compat_l n m p : n > m -> p > 0 -> p * n > p * m.
Proof. intros H H1; red; apply mult_lt_compat_l; auto. Qed.

Theorem mult_lt_compat_rev_l1 n m p : p * n < p * m -> 0 < p.
Proof. case p; auto with arith. Qed.

Theorem mult_lt_compat_rev_l2 n m p : p * n < p * m -> n < m.
Proof.
intros H; case (Nat.le_gt_cases m n); auto with arith; intros H1.
absurd (p * n < p * m); auto with arith.
apply Nat.le_ngt; apply Nat.mul_le_mono_l; auto.
Qed.

Theorem mult_gt_compat_rev_l1 n m p : p * n > p * m -> p > 0.
Proof. case p; auto with arith. Qed.

Theorem mult_gt_compat_rev_l2 n m p : p * n > p * m -> n > m.
Proof.
intros H; case (Nat.le_gt_cases n m); auto with arith; intros H1.
absurd (p * n > p * m); auto with arith.
Qed.

Theorem mult_le_compat_rev_l n m p : p * n <= p * m -> 0 < p -> n <= m.
Proof.
intros H H1; case (Nat.le_gt_cases n m); auto with arith.
intros H2; absurd (p * n <= p * m); auto with arith.
apply Nat.lt_nge; apply mult_lt_compat_l; auto.
Qed.

Theorem mult_ge_compat_rev_l n m p : p * n >= p * m -> 0 < p -> n >= m.
Proof.
intros H H1; case (Nat.le_gt_cases m n); auto with arith; intros H2.
absurd (p * n >= p * m); auto with arith.
unfold ge; apply Nat.lt_nge; apply mult_lt_compat_l; auto.
Qed.

Theorem lt_mult_0 a b : 0 < a -> 0 < b -> 0 < a * b.
Proof.
case a ; case b; simpl; auto with arith.
intros n H1 H2; absurd (0 < 0); auto with arith.
Qed.

Theorem gt_mult_0 a b : a > 0 -> b > 0 -> a * b > 0.
Proof. intros H1 H2; red; apply lt_mult_0; auto with arith. Qed.

Theorem lt_mult_rev_0_l a b : 0 < a * b -> 0 < a .
Proof. case a; simpl; auto with arith. Qed.

Theorem lt_mult_rev_0_r a b : 0 < a * b -> 0 < b .
Proof.
case b; simpl; auto with arith.
rewrite Nat.mul_0_r; auto with arith.
Qed.

Theorem gt_mult_rev_0_l a b : a * b > 0 -> a > 0.
Proof. case a; simpl; auto with arith. Qed.

Theorem gt_mult_rev_0_r a b : a * b > 0 -> b > 0.
Proof.
case b; simpl; auto with arith.
rewrite Nat.mul_0_r; auto with arith.
Qed.

Theorem le_0_eq_0 n : n <= 0 -> n = 0.
Proof. case n; auto with arith. Qed.

Definition le_gt_trans := Nat.lt_le_trans.
Definition gt_le_trans := Nat.le_lt_trans.
Definition mult_le_compat_l := Nat.mul_le_mono_l.
Definition plus_le_compat_l := Nat.add_le_mono_l.
Definition plus_le_reg_l := Nat.add_le_mono_l.
Definition le_trans := Nat.le_trans.
Definition plus_lt_reg_l := Nat.add_lt_mono_l.
Definition plus_gt_reg_l := Nat.add_lt_mono_l.
Definition plus_lt_compat_l := Nat.add_lt_mono_l.
Definition plus_gt_compat_l :=  Nat.add_lt_mono_l.
