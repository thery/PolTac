Require Import NArith.

Open Scope N_scope.

Theorem Lt_diff_Gt: Lt <> Gt.
Proof. discriminate. Qed.

Theorem Eq_diff_Gt: Eq <> Gt.
Proof. discriminate. Qed.

Close Scope N_scope.

Hint Extern 4 (N.lt ?X1 ?X2) => exact (refl_equal Lt).
Hint Extern 4 (N.le ?X1 ?X2) => exact Lt_diff_Gt || exact Eq_diff_Gt.
