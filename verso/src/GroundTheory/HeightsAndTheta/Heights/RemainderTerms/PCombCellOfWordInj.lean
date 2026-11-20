import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem Comb.pcnt_lt_of_lt_of_eq {m n : ℕ} (w : Fin n → Fin m) {s t : Fin n} (hst : s < t)
    (i : Fin m) (hs : w s = i) : pcnt w s i < pcnt w t i := by
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨s, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨Fin.lt_def.mp hst, hs⟩
    · simp
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 (Fin.lt_def.mp hst), hx.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem CombCellOfWordInj.proof : CombCellOfWordInj.Statement := by
  intro m n w s t h
  simp only [cellOfWord, Prod.mk.injEq] at h
  obtain ⟨hw, hc⟩ := h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w s) rfl
    rw [hc, hw] at this
    exact lt_irrefl _ (hw ▸ this)
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w t) rfl
    rw [← hc, ← hw] at this
    exact lt_irrefl _ (hw ▸ this)

end GroundTheory.Heights₂.Heights.RestTerms
