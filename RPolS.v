From Stdlib Require Import QArith_base Qcanon.
Require Import RAux.
Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.

Definition Qc2R_can a := 
  if (Pos.eqb (Qden a) 1) then IZR (Qnum a)  
  else if (Z.eqb (Qnum a) 1) then Rinv (IZR (Z.pos (Qden a)))  
  else (IZR (Qnum a) / IZR (Z.pos (Qden a)))%R.

Definition Rconvert_back (e : PExpr Qc) (l : list R) : R :=
  convert_back Qc R R0 Rplus Rminus Rmult Ropp Qc2R_can l e.

Definition is_Qc1 := Qc_eq_bool 1.
Definition is_Qc0 := Qc_eq_bool 0.
Definition is_Qcpos x := Qle_bool 0 (this x).
Definition is_Qcdiv (x y : Qc) := true.

Definition Rsimpl_minus (e : PExpr Qc) :=
  simpl_minus
    Qc Qcplus Qcmult Qcopp 0 1 is_Qc1 is_Qc0 is_Qcpos is_Qcdiv Qcdiv e.

Definition Rsimpl (e : PExpr Qc) :=
  simpl
    Qc Qcplus Qcmult Qcopp 0 1 is_Qc1 is_Qc0 is_Qcpos is_Qcdiv Qcdiv e.

Ltac rs term1 term2 :=
  let term := constr:(Rminus term1 term2) in
  let rfv := FV RCst Rplus Rmult Rminus Ropp term (@nil R) in
  let fv := Trev rfv in
  let expr1 := mkPolexpr Qc RCst Rplus Rmult Rminus Ropp term1 fv in
  let expr2 := mkPolexpr Qc RCst Rplus Rmult Rminus Ropp term2 fv in
  let re := (eval vm_compute in (Rsimpl_minus (PEsub expr1 expr2))) in
  let expr3 := match re with (PEsub ?X1 _) => X1 end in
  let expr4 := match re with (PEsub _ ?X1) => X1 end in
  let re1 := constr:(PEsub expr1 expr3) in
  let re1' :=
      (eval
         unfold
         Rconvert_back, convert_back, pos_nth, jump,
       hd, tl, Qc2R_can, Qcanon.this, Q2Qc, Qreduction.Qred,
        inject_Z, Z.eqb, Qden, Qnum, Z2R, P2R,
       Pos.eqb, Z.ggcd, Z.abs, snd, Z.to_pos, Z.sgn,
       Pos.ggcd, Pos.size_nat, Nat.add, Pos.ggcdn
 in (Rconvert_back (PEadd re1 expr3) fv))
  in
  let re1'' := (eval lazy beta in re1') in
  let
    re2' :=
    (eval
       unfold
       Rconvert_back, convert_back, pos_nth, jump,
     hd, tl, Qc2R_can, Qcanon.this, Q2Qc, Qreduction.Qred,
     inject_Z, Z.eqb, Qden, Qnum, Z2R, P2R,
     Pos.eqb, Z.ggcd, Z.abs, snd, Z.to_pos, Z.sgn,
     Pos.ggcd, Pos.size_nat, Nat.add, Pos.ggcdn
     in (Rconvert_back (PEadd re1 expr4) fv))
  in
  let re2'' := (eval lazy beta in re2') in
  replace2_tac term1 term2 re1'' re2''; [idtac| try field | try field].

Ltac rpols :=
  match goal with
  | |- (?X1 = ?X2)%R => rs X1 X2; try apply Rplus_eq_compat_l
  | |- (?X1 <> ?X2)%R => rs X1 X2; apply Rplus_neg_compat_l
  | |- Rlt ?X1 ?X2 => rs X1 X2; apply Rplus_lt_compat_l
  | |- Rgt ?X1 ?X2 => rs X1 X2; apply Rplus_gt_compat_l
  | |- Rle ?X1 ?X2 => rs X1 X2; apply Rplus_le_compat_l
  | |- Rge ?X1 ?X2 => rs X1 X2; apply Rplus_ge_compat_l
  | _ => fail
  end.

Ltac hyp_rpols H :=
  generalize H;
  let tmp := fresh "tmp" in
  match (type of H) with
  | (?X1 = ?X2)%R =>
    rs X1 X2; intros tmp; generalize (Rplus_eq_reg_l _ _ _ tmp); clear H tmp; intro H
  | (?X1 <> ?X2)%nat =>
    rs X1 X2; intros tmp; generalize (Rplus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
  | Rlt ?X1 ?X2 =>
    rs X1 X2; intros tmp; generalize (Rplus_lt_reg_r _ _ _ tmp); clear H tmp; intro H
  | Rgt ?X1 ?X2 =>
    rs X1 X2; intros tmp; generalize (Rplus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
  | Rle ?X1 ?X2 =>
    rs X1 X2; intros tmp; generalize (Rplus_le_reg_l _ _ _ tmp); clear H tmp; intro H
  | Rge ?X1 ?X2 =>
    rs X1 X2; intros tmp; generalize (Rplus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
  | _ => fail
  end.
