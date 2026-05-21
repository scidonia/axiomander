Require Import ZArith String List Lia. Import ListNotations. Open Scope Z_scope.

Goal True /\ (True /\ (True /\ True)).
Proof.
  split.
  - constructor.
  - split.
    -- constructor.
    -- split.
      --- constructor.
      --- constructor.
Qed.
