Require Export ZArith.

Theorem Zplus_eq_compat_l: forall a b c:Z, (b = c -> a + b = a + c)%Z.
intros; apply f_equal2 with (f := Zplus); auto.
Qed.

Theorem Zplus_neg_compat_l: forall a b c: Z, (b <> c -> a + b <> a + c)%Z.
intros a b c H H1; case H.
apply Zplus_reg_l with a; auto.
Qed.

Theorem Zplus_ge_compat_l: forall n m p : Z, (n >= m -> p + n >= p + m)%Z.
intros n m p H; apply Z.le_ge; apply Zplus_le_compat_l; auto; apply Z.ge_le; auto.
Qed.

Theorem Zplus_neg_reg_l: forall a b c: Z,  (a + b <> a + c -> b <> c)%Z.
intros a b c H H1; case H; subst; auto.
Qed.

Theorem Zplus_ge_reg_l: forall n m p : Z, (p + n >= p + m -> n >= m)%Z.
intros n m p H; apply Z.le_ge; apply Zplus_le_reg_l with p; auto; apply Z.ge_le; auto.
Qed.

(* Theorems to simplify the goal 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Zle_sign_pos_pos: forall x y: Z, (0 <= x -> 0 <= y  -> 0 <= x * y)%Z.
auto with zarith.
Qed.

Theorem Zle_sign_neg_neg: forall x y: Z, (x <= 0 -> y <= 0  -> 0 <= x * y)%Z.
intros x y H1 H2; replace (x * y)%Z with (-x * -y)%Z; auto with zarith; ring.
Qed.

Theorem Zopp_le: forall n m, (m <= n -> -n <= -m)%Z.
auto with zarith.
Qed.

Theorem Zle_pos_neg: forall x, (0 <= -x -> x <= 0)%Z.
auto with zarith.
Qed.

Theorem Zle_sign_pos_neg: forall x y: Z, (0 <= x -> y <= 0  -> x * y <= 0)%Z.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; ring.
Qed.

Theorem Zle_sign_neg_pos: forall x y: Z, (x <= 0 -> 0 <= y  -> x * y <= 0)%Z.
intros x y H1 H2; apply Zle_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; ring.
Qed.


Theorem Zlt_sign_pos_pos: forall x y: Z, (0 < x -> 0 < y  -> 0 < x * y)%Z.
intros; apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_sign_neg_neg: forall x y: Z, (x < 0 -> y < 0  -> 0 < x * y)%Z.
intros x y H1 H2; replace (x * y)%Z with (-x * -y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_pos_neg: forall x, (0 < -x -> x < 0)%Z.
auto with zarith.
Qed.

Theorem Zlt_sign_pos_neg: forall x y: Z, (0 < x -> y < 0  -> x * y < 0)%Z.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (x * (- y))%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zlt_sign_neg_pos: forall x y: Z, (x < 0 -> 0 < y  -> x * y < 0)%Z.
intros x y H1 H2; apply Zlt_pos_neg; replace (- (x * y))%Z with (-x * y)%Z; auto with zarith; try ring.
apply Zmult_lt_O_compat; auto with zarith.
Qed.

Theorem Zge_sign_neg_neg: forall x y: Z, (0 >= x -> 0 >= y  -> x * y >= 0)%Z.
intros; apply Z.le_ge; apply Zle_sign_neg_neg; auto with zarith.
Qed.

Theorem Zge_sign_pos_pos: forall x y: Z, (x >= 0 -> y >= 0  -> x * y >= 0)%Z.
intros; apply Z.le_ge; apply Zle_sign_pos_pos; auto with zarith.
Qed.

Theorem Zge_neg_pos: forall x, (0 >= -x -> x >= 0)%Z.
auto with zarith.
Qed.

Theorem Zge_sign_neg_pos: forall x y: Z, (0 >= x -> y >= 0  -> 0>= x * y)%Z.
intros; apply Z.le_ge; apply Zle_sign_neg_pos; auto with zarith.
Qed.

Theorem Zge_sign_pos_neg: forall x y: Z, (x >= 0 -> 0 >= y  -> 0 >= x * y)%Z.
intros; apply Z.le_ge; apply Zle_sign_pos_neg; auto with zarith.
Qed.


Theorem Zgt_sign_neg_neg: forall x y: Z, (0 > x -> 0 > y  -> x * y > 0)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_neg_neg; auto with zarith.
Qed.

Theorem Zgt_sign_pos_pos: forall x y: Z, (x > 0 -> y > 0  -> x * y > 0)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_pos_pos; auto with zarith.
Qed.

Theorem Zgt_neg_pos: forall x, (0 > -x -> x > 0)%Z.
auto with zarith.
Qed.

Theorem Zgt_sign_neg_pos: forall x y: Z, (0 > x -> y > 0  -> 0> x * y)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_neg_pos; auto with zarith.
Qed.

Theorem Zgt_sign_pos_neg: forall x y: Z, (x > 0 -> 0 > y  -> 0 > x * y)%Z.
intros; apply Z.lt_gt; apply Zlt_sign_pos_neg; auto with zarith.
Qed.

(* Theorems to simplify the hyp 0 ? x * y and x * y ? 0 where ? is < > <= >= *)

Theorem Zle_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 <= x * y -> 0 <= y)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_neg; auto.
Qed.

Theorem Zle_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 <= x * y ->  y <= 0)%Z.
intros x y H1 H2; case (Zle_or_lt y  0); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_neg_pos; auto.
Qed.

Theorem Zle_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y <= 0 -> y <= 0)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_pos_pos; auto.
Qed.

Theorem Zle_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y <= 0 ->  0 <= y)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
apply Zlt_not_le;apply Zlt_sign_neg_neg; auto.
Qed.

Theorem Zge_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y >= 0 -> y >= 0)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_pos_pos_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y  >= 0->  0 >= y)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_neg_neg_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 >= x * y -> 0 >= y)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_pos_neg_rev with x; auto with zarith.
Qed.

Theorem Zge_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 >= x * y ->  y >= 0)%Z.
intros x y H1 H2; apply Z.le_ge; apply Zle_sign_neg_pos_rev with x; auto with zarith.
Qed.

Theorem Zlt_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 < x * y -> 0 < y)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_pos_neg; auto with zarith.
Qed.

Theorem Zlt_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 < x * y ->  y < 0)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_pos; auto with zarith.
Qed.

Theorem Zlt_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y < 0 -> y < 0)%Z.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_pos_pos; auto with zarith.
Qed.

Theorem Zlt_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y < 0 ->  0 < y)%Z.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_neg; auto with zarith.
Qed.

Theorem Zgt_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y > 0 -> y > 0)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_pos_pos_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y  > 0->  0 > y)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_neg_neg_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 > x * y -> 0 > y)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_pos_neg_rev with x; auto with zarith.
Qed.

Theorem Zgt_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 > x * y ->  y > 0)%Z.
intros x y H1 H2; apply Z.lt_gt; apply Zlt_sign_neg_pos_rev with x; auto with zarith.
Qed.

(* Theorem to simplify x * y ? x * z where ? is < > <= >= *)

Theorem Zmult_le_neg_compat_l:
  forall n m p : Z, (m <= n)%Z -> (p <= 0)%Z -> (p * n <= p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_le; apply Zmult_le_compat_l; auto with zarith.
Qed.

Theorem Zopp_lt: forall n m, (m < n -> -n < -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_lt_neg_compat_l:
  forall n m p : Z, (m < n)%Z -> (p < 0)%Z -> (p * n < p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_lt; apply Zmult_lt_compat_l; auto with zarith.
Qed.

Theorem Zopp_ge: forall n m, (m >= n -> -n >= -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_ge_neg_compat_l:
  forall n m p : Z, (m >= n)%Z -> (0 >= p)%Z -> (p * n >= p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_ge; apply Zmult_ge_compat_l; auto with zarith.
Qed.

Theorem Zopp_gt: forall n m, (m > n -> -n > -m)%Z.
auto with zarith.
Qed.

Theorem Zmult_gt_neg_compat_l:
  forall n m p : Z, (m > n)%Z -> (0 > p)%Z -> (p * n > p * m)%Z.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
apply Zopp_gt; apply Zmult_gt_compat_l; auto with zarith.
Qed.


(* Theorem to simplify a hyp x * y ? x * z where ? is < > <= >= *)


Theorem Zmult_le_compat_l_rev:
  forall n m p : Z, (0 < p)%Z -> (p * n <= p * m)%Z -> (n <= m)%Z.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
apply Zlt_not_le; apply Zmult_lt_compat_l; auto.
Qed.

Theorem Zmult_le_neg_compat_l_rev:
  forall n m p : Z, (p < 0)%Z -> (p * n <= p * m)%Z -> (m <= n)%Z.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
apply Zlt_not_le; apply Zmult_lt_neg_compat_l; auto.
Qed.

Theorem Zmult_lt_compat_l_rev:
  forall n m p : Z, (0 < p)%Z -> (p * n < p * m)%Z -> (n < m)%Z.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_compat_l; auto with zarith.
Qed.

Theorem Zmult_lt_neg_compat_l_rev:
  forall n m p : Z, (p < 0)%Z -> (p * n < p * m)%Z -> (m < n)%Z.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
apply Zle_not_lt; apply Zmult_le_neg_compat_l; auto with zarith.
Qed.

Theorem Zmult_ge_compat_l_rev:
  forall n m p : Z, (p > 0)%Z -> (p * n >= p * m)%Z -> (n >= m)%Z.
intros n m p H H1;
 apply Z.le_ge; apply Zmult_le_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_ge_neg_compat_l_rev:
  forall n m p : Z, (0 > p)%Z -> (p * n >= p * m)%Z -> (m >= n)%Z.
intros n m p H H1;
 apply Z.le_ge; apply Zmult_le_neg_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_gt_compat_l_rev:
  forall n m p : Z, (p > 0)%Z -> (p * n > p * m)%Z -> (n > m)%Z.
intros n m p H H1;
 apply Z.lt_gt; apply Zmult_lt_compat_l_rev with p; auto with zarith.
Qed.

Theorem Zmult_gt_neg_compat_l_rev:
  forall n m p : Z, (0 > p)%Z -> (p * n > p * m)%Z -> (m > n)%Z.
intros n m p H H1;
 apply Z.lt_gt; apply Zmult_lt_neg_compat_l_rev with p; auto with zarith.
Qed.
