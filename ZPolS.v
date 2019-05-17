Require Import ZAux.
Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.


Definition Zconvert_back (e : PExpr Z) (l : list Z) : Z :=
  convert_back Z Z Z0 Zplus Zminus Zmult Z.opp (fun (x : Z) => x) l e.

Definition Zsimpl (e : PExpr Z) :=
  simpl
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.

Definition Zsimpl_minus (e : PExpr Z) :=
  simpl_minus
    Z Zplus Zmult Z.opp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Z.div e.

Ltac zs term1 term2 :=
  let term := constr:(Zminus term1 term2) in
  let rfv := FV ZCst Zplus Zmult Zminus Z.opp term (@nil Z) in
  let fv := Trev rfv in
  let expr1 := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp term1 fv in
  let expr2 := mkPolexpr Z ZCst Zplus Zmult Zminus Z.opp term2 fv in
  let re := (eval vm_compute in (Zsimpl_minus (PEsub expr1 expr2))) in
  let expr3 := match re with (PEsub ?X1 _) => X1 end in
  let expr4 := match re with (PEsub _ ?X1) => X1 end in
  let re1 := (eval vm_compute in (Zsimpl (PEsub expr1 expr3))) in
  let re1' :=
      (eval
         unfold
         Zconvert_back, convert_back, pos_nth, jump,
       hd, tl in (Zconvert_back (PEadd re1 expr3) fv))
  in
  let re1'' := (eval lazy beta in re1') in
  let re2' :=
      (eval
         unfold
         Zconvert_back, convert_back, pos_nth, jump,
       hd, tl in (Zconvert_back (PEadd re1 expr4) fv))
  in
  let re2'' := (eval lazy beta in re2') in
  replace2_tac term1 term2 re1'' re2''; [idtac | ring | ring].

Ltac zpols :=
  match goal with
  | |- (?X1 = ?X2)%Z => zs X1 X2; apply Zplus_eq_compat_l
  | |- (?X1 <> ?X2)%Z => zs X1 X2; apply Zplus_neg_compat_l
  | |- Z.lt ?X1 ?X2 => zs X1 X2; apply Zplus_lt_compat_l
  | |- Z.gt ?X1 ?X2 => zs X1 X2; apply Zplus_gt_compat_l
  | |- Z.le ?X1 ?X2 => zs X1 X2; apply Zplus_le_compat_l
  | |- Z.ge ?X1 ?X2 => zs X1 X2; apply Zplus_ge_compat_l
  | _ => fail
  end.

Ltac hyp_zpols H :=
  generalize H;
  let tmp := fresh "tmp" in
  match (type of H) with
  | (?X1 = ?X2)%Z =>
    zs X1 X2; intros tmp; generalize (Zplus_reg_l _ _ _ tmp); clear H tmp; intro H
  | (?X1 <> ?X2)%nat =>
    zs X1 X2; intros tmp; generalize (Zplus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
  | Z.lt ?X1 ?X2 =>
    zs X1 X2; intros tmp; generalize (Zplus_lt_reg_l _ _ _ tmp); clear H tmp; intro H
  | Z.gt ?X1 ?X2 =>
    zs X1 X2; intros tmp; generalize (Zplus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
  | Z.le ?X1 ?X2 =>
    zs X1 X2; intros tmp; generalize (Zplus_le_reg_l _ _ _ tmp); clear H tmp; intro H
  | Z.ge ?X1 ?X2 =>
    zs X1 X2; intros tmp; generalize (Zplus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
  | _ => fail
  end.
