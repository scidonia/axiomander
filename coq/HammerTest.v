Require Import ZArith.
From Hammer Require Import Hammer.
Open Scope Z_scope.
Set Hammer ATPLimit 30.

Theorem max_z_goal : forall a b, 0 <= a -> 0 <= b ->
  (Z.leb b a = true -> a <= a /\ b <= a) /\
  (Z.leb b a = false -> a <= b /\ b <= b).
Proof.
  hammer.
Qed.
