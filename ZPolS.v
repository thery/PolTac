Require Import PolSBase.
Require Import PolAuxList.
Require Import PolAux.



Definition Zconvert_back (e : PExpr Z) (l : list Z) : Z :=
   convert_back Z Z Z0 Zplus Zminus Zmult Zopp (fun (x : Z) => x) l e.

Definition Zsimpl (e : PExpr Z)  :=
   simpl
      Z Zplus Zmult Zopp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Zdiv e. 

Definition Zsimpl_minus (e : PExpr Z) :=
   simpl_minus
    Z Zplus Zmult Zopp Z0 1%Z is_Z1 is_Z0 is_Zpos is_Zdiv Zdiv e. 

Ltac
zs term1 term2 :=
let term := constr:(Zminus term1 term2) in
let rfv := FV ZCst Zplus Zmult Zminus Zopp term (@nil Z) in
let fv := Trev rfv in
let expr1 := mkPolexpr Z ZCst Zplus Zmult Zminus Zopp term1 fv in
let expr2 := mkPolexpr Z ZCst Zplus Zmult Zminus Zopp term2 fv in
let re := eval compute in (Zsimpl_minus (PEsub expr1 expr2)) in
let expr3 := match re with (PEsub ?X1 _) => X1 end in
let expr4 := match re with (PEsub _ ?X1 ) => X1 end in
let re1 := eval compute in (Zsimpl (PEsub expr1 expr3)) in
let
 re1' :=
  eval
     unfold
      Zconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Zconvert_back (PEadd re1 expr3) fv) in
let re1'' := eval lazy beta in re1' in
let
 re2' :=
  eval
     unfold
      Zconvert_back, convert_back,  pos_nth,  jump, 
         hd,  tl in (Zconvert_back (PEadd re1 expr4) fv) in
let re2'' := eval lazy beta in re2' in 
replace2_tac term1 term2 re1'' re2''; [idtac | ring | ring].



Ltac
zpols :=
match goal with
| |- (?X1 = ?X2)%Z =>
zs X1 X2; apply Zplus_eq_compat_l
| |- (?X1 <> ?X2)%Z =>
zs X1 X2; apply Zplus_neg_compat_l
| |- Zlt ?X1 ?X2 =>
zs X1 X2; apply Zplus_lt_compat_l
| |- Zgt ?X1 ?X2 =>
zs X1 X2; apply Zplus_gt_compat_l
| |- Zle ?X1 ?X2 =>
zs X1 X2; apply Zplus_le_compat_l
| |- Zge ?X1 ?X2 =>
zs X1 X2; apply Zplus_ge_compat_l
| _ => fail end.


Ltac
hyp_zpols H :=
generalize H;
let tmp := fresh "tmp" in
match (type of H) with
   (?X1 = ?X2)%Z =>
zs X1 X2; intros tmp; generalize (Zplus_reg_l _ _ _ tmp); clear H tmp; intro H
|  (?X1 <> ?X2)%nat =>
zs X1 X2; intros tmp; generalize (Zplus_neg_reg_l _ _ _ tmp); clear H tmp; intro H
|  Zlt ?X1 ?X2 =>
zs X1 X2; intros tmp; generalize (Zplus_lt_reg_l _ _ _ tmp); clear H tmp; intro H
|  Zgt ?X1 ?X2 =>
zs X1 X2; intros tmp; generalize (Zplus_gt_reg_l _ _ _ tmp); clear H tmp; intro H
|  Zle ?X1 ?X2 =>
zs X1 X2; intros tmp; generalize (Zplus_le_reg_l _ _ _ tmp); clear H tmp; intro H
|  Zge ?X1 ?X2 =>
zs X1 X2; intros tmp; generalize (Zplus_ge_reg_l _ _ _ tmp); clear H tmp; intro H
| _ => fail end.
