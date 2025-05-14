From Stdlib Require Import QArith_base Qcanon.
From Stdlib Require Import Reals.
Require Import RPolS.
Require Import PolSBase.
Require Import PolFBase.
Require Import PolAux.
Require Import PolAuxList.
Require Import RSignTac.

Definition Qcgcd x y := (Qcdiv x y).

Definition Rfactor :=
  factor Qc Qcplus Qcmult Qcopp 0 1 is_Qc1 is_Qc0 is_Qcpos is_Qcdiv Qcdiv Qcgcd.

Definition Rfactor_minus :=
  factor_sub Qc Qcplus Qcmult Qcopp 0 1 is_Qc1 is_Qc0 is_Qcpos is_Qcdiv Qcdiv Qcgcd.


Ltac Rfactor_term term1 term2 :=
  let term := constr:(Rminus term1 term2) in
  let rfv := FV RCst Rplus Rmult Rminus Ropp term (@nil R) in
  let fv := Trev rfv in
  let expr1 := mkPolexpr Qc RCst Rplus Rmult Rminus Ropp term1 fv in
  let expr2 := mkPolexpr Qc RCst Rplus Rmult Rminus Ropp term2 fv in
  let re := (eval vm_compute in (Rfactor_minus (PEsub expr1 expr2))) in
  let factor := match re with (PEmul ?X1 _) => X1 end in
  let expr3 := match re with (PEmul _ (PEsub ?X1 _)) => X1 end in
  let expr4 := match re with (PEmul _ (PEsub _ ?X1 )) => X1 end in
  let re1' :=
      (eval
         unfold
        Rconvert_back, convert_back, pos_nth, jump,
       hd, tl, Qc2R_can, Qcanon.this, Q2Qc, Qreduction.Qred,
       Z.eqb, Qden, Qnum, Z2R, P2R,
       Pos.eqb, Z.ggcd, Z.abs, snd, Z.to_pos, Z.sgn,
       Pos.ggcd, Pos.size_nat, Nat.add, Pos.ggcdn
       in (Rconvert_back (PEmul factor expr3) fv)) in
  let re1'' := (eval lazy beta in re1')
  in
  let re2' :=
      (eval
         unfold
        Rconvert_back, convert_back, pos_nth, jump,
       hd, tl, Qc2R_can, Qcanon.this, Q2Qc, Qreduction.Qred,
      Z.eqb, Qden, Qnum, Z2R, P2R,
       Pos.eqb, Z.ggcd, Z.abs, snd, Z.to_pos, Z.sgn,
       Pos.ggcd, Pos.size_nat, Nat.add, Pos.ggcdn
      in (Rconvert_back (PEmul factor expr4) fv)) in
  let re2'' := (eval lazy beta in re2')
  in
  replace2_tac term1 term2 re1'' re2''; [idtac | ring | ring].

Ltac rpolf :=
  progress
    (try match goal with
         | |- (?X1 = ?X2)%R => Rfactor_term X1 X2
         | |- (?X1 <> ?X2)%R => Rfactor_term X1 X2
         | |- Rlt ?X1 ?X2 => Rfactor_term X1 X2
         | |- Rgt ?X1 ?X2 => Rfactor_term X1 X2
         | |- Rle ?X1 ?X2 => Rfactor_term X1 X2
         | |- Rge ?X1 ?X2 => Rfactor_term X1 X2
         | _ => fail end);
  try rsign_tac; try repeat (rewrite Rmult_1_l || rewrite Rmult_1_r).

Ltac hyp_rpolf H :=
  progress
    (generalize H;
     try match type of H with
         | (?X1 = ?X2)%R => Rfactor_term X1 X2
         | (?X1 <> ?X2)%R => Rfactor_term X1 X2
         | Rlt ?X1 ?X2 => Rfactor_term X1 X2
         | Rgt ?X1 ?X2 => Rfactor_term X1 X2
         | Rle ?X1 ?X2 => Rfactor_term X1 X2
         | Rge ?X1 ?X2 => Rfactor_term X1 X2
         | _ => fail end);
  clear H; intros H;
  try hyp_rsign_tac H; try repeat rewrite Rmult_1_l in H.
