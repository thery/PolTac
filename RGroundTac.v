Require Import Qcanon Qreals.
Require Import Reals.
Require Import PolAux.

Ltac RCst0 t :=
  match t with
  | R0 => constr:(0)
  | R1 => constr:(1)
  | Rplus ?e1 ?e2 =>
    match (RCst0 e1) with
    | ?e3 =>
      match (RCst0 e2) with
      | ?e4 => constr:(Qplus e3 e4)
      end
    end
  | Rminus ?e1 ?e2 =>
    match (RCst0 e1) with
    | ?e3 =>
      match (RCst0 e2) with
      | ?e4 => constr:(Qminus e3 e4)
      end
    end
  | Rmult ?e1 ?e2 =>
    match (RCst0 e1) with
    | ?e3 =>
      match (RCst0 e2) with
      | ?e4 => constr:(Qmult e3 e4)
      end
    end
  | Ropp ?e1 =>
    match (RCst0 e1) with
    | ?e3 => constr:(Qopp e3)
    end
  | Rinv ?e1 =>
    match (RCst0 e1) with
    | ?e3 => constr:(Qinv e3)
    end
  | Rdiv ?e1 ?e2 =>
    match (RCst0 e1) with
    | ?e3 =>
      match (RCst0 e2) with
      | ?e4 => constr:(Qdiv e3 e4)
      end
    end
  | IZR ?e1 =>
    match (ZCst e1) with
    | ?e3 => constr: (inject_Z e3)
    end
  | _ => constr:(0%Q)
  end.

Ltac rground_tac :=
  match goal with
  | |- (?X1 <= ?X2)%R =>
    let r1 := RCst0 X1 in
    let r2 := RCst0 X2 in
    replace X1 with (Q2R r1) by (compute; field);
    replace X2 with (Q2R r2) by (compute; field);
    apply Qle_Rle;
    red; apply refl_equal || intros; discriminate
  | |- (?X1 < ?X2)%R =>
    let r1 := RCst0 X1 in
    let r2 := RCst0 X2 in
    replace X1 with (Q2R r1) by (compute; field);
    replace X2 with (Q2R r2) by (compute; field);
    apply Qlt_Rlt;
    red; apply refl_equal || intros; discriminate
  | |- (?X1 >= ?X2)%R =>
    let r1 := RCst0 X1 in
    let r2 := RCst0 X2 in
    replace X1 with (Q2R r1) by (compute; field); 
    replace X2 with (Q2R r2) by (compute; field);
    apply Qle_Rle;
    red; apply refl_equal || intros; discriminate
  | |- (?X1 > ?X2)%R =>
    let r1 := RCst0 X1 in
    let r2 := RCst0 X2 in
    replace X1 with (Q2R r1) by (compute; field); 
    replace X2 with (Q2R r2) by (compute; field);
    apply Qlt_Rlt;
    red; apply refl_equal || intros; discriminate
  end.

Global Hint Extern 4 (_ <= _)%R => rground_tac: real.
Global Hint Extern 4 (_ < _)%R => rground_tac: real.
Global Hint Extern 4 (_ >= _)%R => rground_tac: real.
Global Hint Extern 4 (_ > _)%R => rground_tac: real.
