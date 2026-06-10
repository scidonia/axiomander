From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SnakeletLang SnakeletWp.

Section test.
  Context `{!snakelet_heapGS_gen hlc Σ}.
  Goal ∀ s E (Φ : sn_val → iProp Σ) (v : sn_val), Φ v -∗ WP Val v @ s; E {{ Φ }}.
  Proof.
    iIntros (s E Φ v) "HΦ".
    match goal with |- WP ?e _ _ {{ _ }} => idtac e end.
  Abort.
End test.
