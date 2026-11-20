import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Ydd5.main :
    ∀ {I : Type} (s : Finset I) (c : ℝ),
      (0 : ℝ) < c → ∀ (f : I → ℝ), (∀ (i : I), (0 : ℝ) < f i) → ∃ (ρ : ℝ), (0 : ℝ) < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i := by
  intro I s c hc f hf
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨c, hc, le_rfl, by simp⟩
  · intro a t _ ih
    obtain ⟨ρ, h0, h1, h2⟩ := ih
    refine ⟨min ρ (f a), lt_min h0 (hf a), (min_le_left _ _).trans h1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 i hi)
