Require Export Reals.

Open Scope R_scope.

Theorem Rplus_eq_compat_l a b c : b = c -> a + b = a + c.
Proof. congruence. Qed.

Theorem Rplus_neg_compat_l a b c : b <> c -> a + b <> a + c.
Proof.
now intros * H; contradict H; apply Rplus_eq_reg_l with a.
Qed.

Theorem Rplus_ge_compat_l n m p : n >= m -> p + n >= p + m.
Proof.
now intros; apply Rle_ge; apply Rplus_le_compat_l; apply Rge_le.
Qed.

Theorem Rplus_neg_reg_l a b c : a + b <> a + c -> b <> c.
Proof. congruence. Qed.

Theorem Rplus_ge_reg_l n m p : p + n >= p + m -> n >= m.
Proof.
now intros; apply Rle_ge; apply Rplus_le_reg_l with p; apply Rge_le.
Qed.

(* Theorems to simplify the goal 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. intros; apply Rmult_le_pos; auto with real. Qed.

Theorem Rle_sign_neg_neg x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
intros; replace (x * y) with (-x * -y) by ring.
now apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_pos_neg x : 0 <= -x -> x <= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_le_contravar; rewrite Ropp_0.
Qed.

Theorem Rle_sign_pos_neg x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof.
intros; apply Rle_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
now apply Rmult_le_pos; auto with real.
Qed.

Theorem Rle_sign_neg_pos x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
intros; apply Rle_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
now apply Rmult_le_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_pos x y : 0 < x -> 0 < y -> 0 < x * y.
Proof. intros; apply Rmult_lt_0_compat; auto with real. Qed.

Theorem Rlt_sign_neg_neg x y : x < 0 -> y < 0  -> 0 < x * y.
Proof.
intros; replace (x * y) with (-x * -y) by ring.
now apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rlt_pos_neg x : 0 < -x -> x < 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_lt_contravar; rewrite Ropp_0; auto with real.
Qed.

Theorem Rlt_sign_pos_neg x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
apply Rmult_lt_0_compat; trivial.
replace 0 with (-0); auto with real.
Qed.

Theorem Rlt_sign_neg_pos x y : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
now apply Rmult_lt_0_compat; auto with real.
Qed.

Theorem Rge_sign_neg_neg x y : 0 >= x -> 0 >= y -> x * y >= 0.
Proof. intros; apply Rle_ge; apply Rle_sign_neg_neg; auto with real. Qed.

Theorem Rge_sign_pos_pos x y : x >= 0 -> y >= 0 -> x * y >= 0.
Proof. intros; apply Rle_ge; apply Rle_sign_pos_pos; auto with real. Qed.

Theorem Rge_neg_pos x : 0 >= -x -> x >= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Rle_ge; apply Ropp_le_contravar; rewrite Ropp_0; auto with real.
Qed.

Theorem Rge_sign_neg_pos x y : 0 >= x -> y >= 0 -> 0 >= x * y.
Proof. intros; apply Rle_ge; apply Rle_sign_neg_pos; auto with real. Qed.

Theorem Rge_sign_pos_neg x y : x >= 0 -> 0 >= y -> 0 >= x * y.
Proof. intros; apply Rle_ge; apply Rle_sign_pos_neg; auto with real. Qed.

Theorem Rgt_sign_neg_neg x y : 0 > x -> 0 > y -> x * y > 0.
Proof. intros; apply Rlt_sign_neg_neg; auto with real. Qed.

Theorem Rgt_sign_pos_pos x y : x > 0 -> y > 0 -> x * y > 0.
Proof. apply Rlt_sign_pos_pos; auto with real. Qed.

Theorem Rgt_neg_pos x : 0 > -x -> x > 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_lt_contravar; rewrite Ropp_0; auto with real.
Qed.

Theorem Rgt_sign_neg_pos x y : 0 > x -> y > 0 -> 0 > x * y.
Proof. apply Rlt_sign_neg_pos; auto with real. Qed.

Theorem Rgt_sign_pos_neg x y : x > 0 -> 0 > y -> 0 > x * y.
Proof. apply Rlt_sign_pos_neg; auto with real. Qed.

(* Theorems to simplify the hyp 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Rle_sign_pos_pos_rev x y : 0 < x -> 0 <= x * y -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 <= x * y); trivial.
now apply Rlt_not_le;apply Rlt_sign_pos_neg.
Qed.

Theorem Rle_sign_neg_neg_rev x y : x < 0 -> 0 <= x * y -> y <= 0.
Proof.
case (Rle_or_lt y  0); trivial.
intros; absurd (0 <= x * y); trivial.
now apply Rlt_not_le;apply Rlt_sign_neg_pos.
Qed.

Theorem Rle_sign_pos_neg_rev x y : 0 < x -> x * y <= 0 -> y <= 0.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (x * y <= 0); trivial.
now apply Rlt_not_le;apply Rlt_sign_pos_pos.
Qed.

Theorem Rle_sign_neg_pos_rev x y : x < 0 -> x * y <= 0 -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (x * y <= 0); trivial.
now apply Rlt_not_le;apply Rlt_sign_neg_neg.
Qed.

Theorem Rge_sign_pos_pos_rev x y : x > 0 -> x * y >= 0 -> y >= 0.
Proof.
intros; apply Rle_ge; apply Rle_sign_pos_pos_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_neg_rev x y : 0 > x -> x * y >= 0 -> 0 >= y.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_pos_neg_rev x y : x > 0 -> 0 >= x * y -> 0 >= y.
Proof.
intros; apply Rle_ge; apply Rle_sign_pos_neg_rev with x; auto with real.
Qed.

Theorem Rge_sign_neg_pos_rev x y : 0 > x -> 0 >= x * y -> y >= 0.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_pos_rev with x; auto with real.
Qed.

Theorem Rlt_sign_pos_pos_rev x y : 0 < x -> 0 < x * y -> 0 < y.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (0 < x * y); trivial.
apply Rle_not_lt;apply Rle_sign_pos_neg; auto with real.
Qed.

Theorem Rlt_sign_neg_neg_rev x y : x < 0 -> 0 < x * y -> y < 0.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 < x * y); trivial.
apply Rle_not_lt;apply Rle_sign_neg_pos; auto with real.
Qed.

Theorem Rlt_sign_pos_neg_rev x y : 0 < x -> x * y < 0 -> y < 0.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (x * y < 0); trivial.
apply Rle_not_lt;apply Rle_sign_pos_pos; auto with real.
Qed.

Theorem Rlt_sign_neg_pos_rev x y : x < 0 -> x * y < 0 -> 0 < y.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (x * y < 0); trivial.
apply Rle_not_lt;apply Rle_sign_neg_neg; auto with real.
Qed.

Theorem Rgt_sign_pos_pos_rev x y : x > 0 -> x * y > 0 -> y > 0.
Proof. intros; apply Rlt_sign_pos_pos_rev with x; auto with real. Qed.

Theorem Rgt_sign_neg_neg_rev x y : 0 > x -> x * y > 0 -> 0 > y.
Proof. intros; apply Rlt_sign_neg_neg_rev with x; auto with real. Qed.

Theorem Rgt_sign_pos_neg_rev x y : x > 0 -> 0 > x * y -> 0 > y.
Proof. intros; apply Rlt_sign_pos_neg_rev with x; auto with real. Qed.

Theorem Rgt_sign_neg_pos_rev x y : 0 > x -> 0 > x * y -> y > 0.
Proof. intros; apply Rlt_sign_neg_pos_rev with x; auto with real. Qed.

(* Theorem to simplify x * y ? x * z where ? is < > <= >= *)

Theorem Rmult_le_compat_l n m p : m <= n -> 0 <= p -> p * m <= p * n.
Proof. auto with real. Qed.

Theorem Rmult_le_neg_compat_l n m p : m <= n -> p <= 0 -> p * n <= p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
auto with real.
Qed.

Theorem Ropp_lt n m : m < n -> -n < -m.
Proof. auto with real. Qed.

Theorem Rmult_lt_neg_compat_l n m p : m < n -> p < 0 -> p * n < p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
auto with real.
Qed.

Theorem Ropp_ge n m : m >= n -> -n >= -m.
Proof. auto with real. Qed.

Theorem Rmult_ge_compat_l n m p : m >= n -> p >= 0 -> p * m >= p * n.
Proof. intros; apply Rle_ge; auto with real. Qed.

Theorem Rmult_ge_neg_compat_l n m p : m >= n -> 0 >= p -> p * n >= p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
auto with real.
Qed.

Theorem Ropp_gt n m : m > n -> -n > -m.
Proof. auto with real. Qed.

Theorem Rmult_gt_compat_l n m p : n > m -> p > 0 -> p * n > p * m.
Proof. unfold Rgt; auto with real. Qed.

Theorem Rmult_gt_neg_compat_l n m p : (m > n) -> (0 > p) -> (p * n > p * m).
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
auto with real.
Qed.

(* Theorem to simplify a hyp x * y ? x * z where ? is < > <= >= *)

Theorem Rmult_le_compat_l_rev n m p : 0 < p -> p * n <= p * m -> n <= m.
Proof.
case (Rle_or_lt n m); trivial.
intros; absurd (p * n <= p * m); trivial.
now apply Rlt_not_le; apply Rmult_lt_compat_l.
Qed.

Theorem Rmult_le_neg_compat_l_rev n m p : p < 0 -> p * n <= p * m -> m <= n.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n <= p * m); trivial.
now apply Rlt_not_le; apply Rmult_lt_neg_compat_l.
Qed.

Theorem Rmult_lt_compat_l_rev n m p : 0 < p -> p * n < p * m -> n < m.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n < p * m); trivial.
now apply Rle_not_lt; apply Rmult_le_compat_l; auto with real.
Qed.

Theorem Rmult_lt_neg_compat_l_rev n m p : p < 0 -> p * n < p * m -> m < n.
Proof.
case (Rle_or_lt n m); trivial.
intros; absurd (p * n < p * m); trivial.
now apply Rle_not_lt; apply Rmult_le_neg_compat_l; auto with real.
Qed.

Theorem Rmult_ge_compat_l_rev n m p : p > 0 -> p * n >= p * m -> n >= m.
Proof.
intros; apply Rle_ge; apply Rmult_le_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_ge_neg_compat_l_rev n m p : 0 > p -> p * n >= p * m -> m >= n.
Proof.
intros; apply Rle_ge; apply Rmult_le_neg_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_compat_l_rev n m p : p > 0 -> p * n > p * m -> n > m.
Proof.
intros; apply Rmult_lt_compat_l_rev with p; auto with real.
Qed.

Theorem Rmult_gt_neg_compat_l_rev n m p : 0 > p -> p * n > p * m -> m > n.
Proof.
intros; apply Rmult_lt_neg_compat_l_rev with p; auto with real.
Qed.
