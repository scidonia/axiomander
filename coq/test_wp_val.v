From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From iris.base_logic.lib Require Export gen_heap.
Require Import SnakeletLang SnakeletWp.

Section test.
  Context (fun_specs : string → list sn_val → sn_val → Prop).
  Context `{!snakelet_heapGS_gen hlc Σ}.
  Let Λ := snakelet_lang fun_specs.

  Goal ∀ s E (Φ : sn_val → iProp Σ) (v : sn_val), Φ v -∗ WP (Val v) @ s; E {{ Φ }}.
  Proof.
    iIntros (s E Φ v) "HΦ".
    Show.
    (* iApply (wp_value' with "HΦ"). *)
  Abort.
End test.
