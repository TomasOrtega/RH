import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_good_without_bad :
    ∀ {P : Type} [DecidableEq P] (Good : Finset P → Prop) (bad : P → Prop), (∀ (S : Finset P) (w : P), Good S → w ∈ S → bad w → Good (S.erase w)) → ∀ S : Finset P, Good S → ∃ T : Finset P, Good T ∧ ∀ w ∈ T, ¬ bad w := by
  intro P _ Good bad h S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    by_cases hb : ∃ w ∈ S, bad w
    · obtain ⟨w, hw, hbw⟩ := hb
      exact ih (S.erase w) (Finset.erase_ssubset hw) (h S w hS hw hbw)
    · exact ⟨S, hS, fun w hw hbw => hb ⟨w, hw, hbw⟩⟩
