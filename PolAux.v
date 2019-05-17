Require Export Replace2.
Require Import NAux ZAux RAux.
Require P.

(* Definition of the opposite for nat *)
Definition Natopp := (fun x:nat => 0%nat).

(* Definition of the opposite for N *)
Definition Nopp := (fun x:N => 0%N).

(* Auxillary functions for Z *)

Definition is_Z0 := Zeq_bool 0.
Definition is_Z1 := Zeq_bool 1.
Definition is_Zpos := Zle_bool 0.
Definition is_Zdiv x y :=
  if Zeq_bool x Z0 then false else Zeq_bool Z0 (Zmod y x).
Definition Zgcd x y :=
  if is_Zdiv x y then x else if is_Zdiv y x then y else 1%Z.

(* Check if a nat is a number *)
Ltac is_NatCst p :=
  match p with
  | O => constr:(true)
  | S ?p' => is_NatCst p'
  | _ => constr:(false)
  end.

(* Convert a Z into a nat if it is a number *)
Ltac NatCst t :=
  match is_NatCst t with
  | false => constr:(false)
  | _ => let res := eval compute in (Z_of_nat t) in constr:(res)
  end.


(* Check if a number is a positive *)
Ltac is_PCst p :=
  match p with
  | xH => constr:(true)
  | xO ?p' => is_PCst p'
  | xI ?p' => is_PCst p'
  | _ => constr:(false)
  end.

(* Check if a N is a number *)
Ltac is_NCst p :=
  match p with
  | N0 => constr:(true)
  | Npos ?p' => is_PCst p'
  | _ => constr:(false)
  end.

(* Convert a Z into a nat if it is a number *)
Ltac NCst t :=
  match is_NCst t with
  | false => constr:(false)
  | _ => let res := eval compute in (Z_of_N t) in constr:(res)
  end.

(* If a number is an integer return itself otherwise false *)
Ltac ZCst t :=
  match t with
  | Z0 => constr:(t)
  | Zpos ?p =>
    match is_PCst p with
    | false => constr:(false)
    | _ => constr:(t)
    end
  | Zneg ?p =>
    match is_PCst p with
    | false => constr:(false)
    | _ => constr:(t)
    end
  | _ => constr:(false)
  end.

(* Check if a number is an integer *)
Ltac is_ZCst t :=
  match t with
  | Z0 => constr:(true)
  | Zpos ?p => is_PCst p
  | Zneg ?p => is_PCst p
  | _ => constr:(false)
  end.

(* Turn a positive into a real *)
Fixpoint P2R (z: positive) {struct z}: R :=
  match z with
  | xH => 1%R
  | xO xH => 2%R
  | xI xH => 3%R
  | xO z1 => (2 * P2R z1)%R
  | xI z1 => (1 + 2 * P2R z1)%R
  end.

(* Turn an integer into a real *)
Definition Z2R (z: Z): R :=
  match z with
  | Z0 => 0%R
  | Zpos z1 => (P2R z1)%R
  | Zneg z1 => (-(P2R z1))%R
  end.

(* Turn a R when possible into a Z *)
Ltac RCst t :=
  match t with
  | R0 => constr:(Z0)
  | R1 => constr:(Zpos xH)
  | Rplus ?e1 ?e2 =>
    match (RCst e1) with
    | false => constr:(false)
    | ?e3 => match (RCst e2) with
            | false => constr:(false)
            | ?e4 =>  eval vm_compute in (Zplus e3  e4)
            end
    end
  | Rminus ?e1 ?e2 =>
    match (RCst e1) with
    | false => constr:(false)
    | ?e3 => match (RCst e2) with
            | false => constr:(false)
            |  ?e4 => eval vm_compute in (Zminus e3  e4)
            end
    end
  | Rmult ?e1 ?e2 =>
    match (RCst e1) with
    | false => constr:(false)
    | ?e3 => match (RCst e2) with
            | false => constr:(false)
            | ?e4 => eval vm_compute in (Zmult e3  e4)
            end
    end
  | Ropp ?e1 =>
    match (RCst e1) with
    | false => constr:(false)
    | ?e3 => eval vm_compute in (Z.opp e3)
    end
  | IZR ?e1 =>
    match (ZCst e1) with
    | false => constr:(false)
    | ?e3 => e3
    end
  | _ => constr:(false)
  end.

(* Remove the Z.abs_nat of a number, unfortunately stops at
   the first Z.abs_nat x where x is not a number *)

Ltac clean_zabs term :=
  match term with
  | context id [(Z.abs_nat ?X)] =>
    match is_ZCst X with
    | true =>
      let x := (eval vm_compute in (Z.abs_nat X)) in
      let y := context id [x] in
      clean_zabs y
    | false => term
    end
  | _ => term
  end.

(* Remove the Z.abs_N of a number, unfortunately stops at
   the first Z.abs_nat x where x is not a number *)

Ltac clean_zabs_N term :=
  match term with
  | context id [(Z.abs_N ?X)] =>
    match is_ZCst X with
    | true =>
      let x := (eval vm_compute in (Z.abs_N X)) in
      let y := context id [x] in
      clean_zabs_N y
    | false => term
    end
  | _ => term
  end.

(* Equality test for Ltac *)

Ltac eqterm t1 t2 :=
  match constr:((t1,t2)) with (?X, ?X) => true | _ => false end.

(* For replace *)

Theorem trans_equal_r : forall (A : Set) (x y z :A), y = z -> x = y -> x = z.
Proof. intros; apply trans_equal with y; auto. Qed.

(* Theorems for nat *)

Open Scope nat_scope.

Theorem plus_eq_compat_l: forall a b c, b = c -> a + b = a + c.
Proof. intros; apply f_equal2 with (f := plus); auto. Qed.

Theorem plus_neg_compat_l: forall a b c, b <> c -> a + b <> a + c.
Proof. intros a b c H H1; case H; apply plus_reg_l with a; auto. Qed.

Theorem plus_ge_compat_l: forall n m p : nat, n >= m -> p + n >= p + m.
Proof. intros n m p H; unfold ge; apply plus_le_compat_l; auto. Qed.

Theorem plus_neg_reg_l: forall a b c,  a + b <> a + c -> b <> c.
Proof. intros a b c H H1; case H; subst; auto. Qed.

Theorem plus_ge_reg_l: forall n m p : nat, p + n >= p + m -> n >= m.
Proof. intros n m p H; unfold ge; apply plus_le_reg_l with p; auto. Qed.

(* For replace *)

Theorem eq_lt_trans_l : forall x y z, x = z -> x < y -> z < y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_lt_trans_r : forall x y z, y = z -> x < y -> x < z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_gt_trans_l : forall x y z, x = z -> x > y -> z > y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_gt_trans_r : forall x y z, y = z -> x > y -> x > z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_le_trans_l : forall x y z, x = z -> x <= y -> z <= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_le_trans_r : forall x y z, y = z -> x <= y -> x <= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_ge_trans_l : forall x y z, x = z -> x >= y -> z >= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_ge_trans_r : forall x y z, y = z -> x >= y -> x >= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem ge_trans: forall x y z, x >= z -> z >= y -> x >= y.
Proof. intros x y z H1 H2; red; apply le_trans with z; auto. Qed.

Close Scope nat_scope.

(* Theorems for N *)

Open Scope N_scope.

Theorem Nplus_eq_compat_l: forall a b c, b = c -> a + b = a + c.
Proof. intros; apply f_equal2 with (f:= Nplus); auto. Qed.

Theorem Nplus_neg_compat_l: forall a b c, b <> c -> a + b <> a + c.
Proof. intros a b c H1 H2; case H1; apply Nplus_reg_l with a; auto. Qed.

Theorem Nplus_lt_compat_l: forall n m p, n < m -> p + n < p + m.
Proof. intros; to_nat; auto with arith. Qed.

Theorem Nplus_gt_compat_l: forall n m p, n > m -> p + n > p + m.
Proof. intros; to_nat; auto with arith. Qed.

Theorem Nplus_le_compat_l: forall n m p, n <= m -> p + n <= p + m.
Proof. intros; to_nat; auto with arith. Qed.

Theorem Nplus_ge_compat_l: forall n m p, n >= m -> p + n >= p + m.
Proof. intros; to_nat; auto with arith. Qed.

Theorem Nplus_neg_reg_l: forall a b c,  a + b <> a + c -> b <> c.
Proof. intros a b c H H1; case H; apply f_equal2 with (f:= Nplus); auto. Qed.

Theorem Nplus_lt_reg_l: forall n m p, p + n < p + m -> n < m.
Proof. intros; to_nat; apply plus_lt_reg_l with nn1; auto with arith. Qed.

Theorem Nplus_gt_reg_l: forall n m p, p + n > p + m -> n > m.
Proof. intros; to_nat; apply plus_gt_reg_l with nn1; auto with arith. Qed.

Theorem Nplus_le_reg_l: forall n m p, p + n <= p + m -> n <= m.
Proof. intros; to_nat; apply plus_le_reg_l with nn1; auto with arith. Qed.

Theorem Nplus_ge_reg_l: forall n m p, p + n >= p + m -> n >= m.
Proof. intros; to_nat; apply plus_ge_reg_l with nn1; auto with arith. Qed.

(* For replace *)
Theorem Neq_lt_trans_l : forall x y z, x = z -> x < y -> z < y.
Proof. intros; subst; auto. Qed.

Theorem Neq_lt_trans_r : forall x y z, y = z -> x < y -> x < z.
Proof. intros; subst; auto. Qed.

Theorem Neq_gt_trans_l : forall x y z, x = z -> x > y -> z > y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Neq_gt_trans_r : forall x y z, y = z -> x > y -> x > z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Neq_le_trans_l : forall x y z, x = z -> x <= y -> z <= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Neq_le_trans_r : forall x y z, y = z -> x <= y -> x <= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Neq_ge_trans_l : forall x y z, x = z -> x >= y -> z >= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Neq_ge_trans_r : forall x y z, y = z -> x >= y -> x >= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Nge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
Proof. intros; to_nat; red; apply le_trans with nn1; auto with arith. Qed.

Close Scope N_scope.

(* Theorems for Z *)

Open Scope Z_scope.

(* For replace *)

Theorem eq_Zlt_trans_l : forall x y z, x = z -> x < y -> z < y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zlt_trans_r : forall x y z, y = z -> x < y -> x < z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zgt_trans_l : forall x y z, x = z -> x > y -> z > y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zgt_trans_r : forall x y z, y = z -> x > y -> x > z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zle_trans_l : forall x y z, x = z -> x <= y -> z <= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zle_trans_r : forall x y z, y = z -> x <= y -> x <= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zge_trans_l : forall x y z, x = z -> x >= y -> z >= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Zge_trans_r : forall x y z, y = z -> x >= y -> x >= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Zge_trans: forall x y z, x >= z -> z >= y -> x >= y.
Proof. intros x y z H1 H2; red; apply Zge_trans with z; auto. Qed.

Close Scope Z_scope.

(* Theorems for R *)

Open Scope R_scope.

(* For replace *)

Theorem eq_Rlt_trans_l : forall x y z, x = z -> x < y -> z < y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rlt_trans_r : forall x y z, y = z -> x < y -> x < z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rgt_trans_l : forall x y z, x = z -> x > y -> z > y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rgt_trans_r : forall x y z, y = z -> x > y -> x > z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rle_trans_l : forall x y z, x = z -> x <= y -> z <= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rle_trans_r : forall x y z, y = z -> x <= y -> x <= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rge_trans_l : forall x y z, x = z -> x >= y -> z >= y.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem eq_Rge_trans_r : forall x y z, y = z -> x >= y -> x >= z.
Proof. intros x y z H; rewrite H; auto. Qed.

Theorem Rge_trans: forall x y z, (x >= z) -> (z >= y) -> (x >= y).
Proof. intros x y z H1 H2; red; apply Rge_trans with z; auto. Qed.

(* For RGroundTac *)

Theorem Z2R_correct: forall p, Z2R p = IZR p.
Proof.
intros p; case p; auto.
intros p1; elim p1; auto.
intros p2 Rec; pattern (Zpos (xI p2)) at 2;
  replace (Zpos (xI p2)) with (2 * (Zpos p2) +1)%Z by auto.
rewrite plus_IZR; rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
intros p2 Rec; pattern (Zpos (xO p2)) at 2;
  replace (Zpos (xO p2)) with (2 * (Zpos p2))%Z by auto.
rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
intros p1; elim p1; auto.
intros p2 Rec; pattern (Zneg (xI p2)) at 2;
  replace (Zneg (xI p2)) with ((2 * (Zneg p2) +  -1))%Z by auto.
rewrite plus_IZR; rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
intros p2 Rec; pattern (Zneg (xO p2)) at 2;
  replace (Zneg (xO p2)) with (2 * (Zneg p2))%Z by auto.
rewrite mult_IZR; rewrite <- Rec.
simpl Z2R; simpl IZR; case p2; intros; simpl (P2R 1); ring.
Qed.

Theorem Z2R_le: forall p q, (p <= q)%Z -> (Z2R p <= Z2R q)%R.
Proof. intros p q; repeat rewrite Z2R_correct; intros; apply IZR_le; auto. Qed.

Theorem Z2R_lt: forall p q, (p < q)%Z -> (Z2R p < Z2R q)%R.
Proof. intros p q; repeat rewrite Z2R_correct; intros; apply IZR_lt; auto. Qed.

Theorem Z2R_ge: forall p q, (p >= q)%Z -> (Z2R p >= Z2R q)%R.
Proof. intros p q; repeat rewrite Z2R_correct; intros; apply IZR_ge; auto. Qed.

Theorem Z2R_gt: forall p q, (p > q)%Z -> (Z2R p > Z2R q)%R.
Proof.
intros p q; repeat rewrite Z2R_correct; intros; red; apply IZR_lt;
  apply Z.gt_lt; auto.
Qed.

Close Scope R_scope.
