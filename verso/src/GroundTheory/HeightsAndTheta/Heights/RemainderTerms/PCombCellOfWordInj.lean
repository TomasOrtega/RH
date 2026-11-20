import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Unfold `pcnt`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [mem_filter, mem_univ, true_and]`.

Conclude with `⟨Fin.lt_def.mp hst, hs⟩`. Simplify using the standard rewrite rules. Introduce `x hx`. Simplify using `only [mem_filter, mem_univ, true_and] at hx ⊢`. Conclude with `⟨lt_trans hx.1 (Fin.lt_def.mp hst), hx.2⟩`.
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
Introduce `m n w s t h`. Simplify using `only [cellOfWord, Prod.mk.injEq] at h`. Take `⟨hw, hc⟩` from `h`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases.

Use `Comb.pcnt_lt_of_lt_of_eq w hlt (w s) rfl` as an intermediate fact. Rewrite `this` using `[hc, hw]`. Conclude with `lt_irrefl _ (hw ▸ this)`. Use `Comb.pcnt_lt_of_lt_of_eq w hlt (w t) rfl` as an intermediate fact. Rewrite `this` using `[← hc, ← hw]`.

Conclude with `lt_irrefl _ (hw ▸ this)`.
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
