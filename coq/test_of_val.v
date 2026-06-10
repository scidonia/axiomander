Require Import SnakeletLang.
Import snakelet_notation.
Goal ∀ v, language.of_val v = Val v.
Proof. intros. reflexivity. Qed.
