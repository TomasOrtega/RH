import Mathlib

namespace GlobalTheory

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem adjoin_roots_of_unity_embeds_complex {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K)
    (t : L0 →+* ℂ) (Z : Set K) (hZ : ∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧
      ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  letI : Algebra L0 K := s.toAlgebra
  letI : Algebra L0 ℂ := t.toAlgebra
  have hint : ∀ z ∈ Z, IsIntegral L0 z := by
    intro z hz
    obtain ⟨n, hn, hzn⟩ := hZ z hz
    exact ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hzn]⟩
  haveI : Algebra.IsAlgebraic L0 (IntermediateField.adjoin L0 Z) :=
    IntermediateField.isAlgebraic_adjoin hint
  let φ : IntermediateField.adjoin L0 Z →ₐ[L0] ℂ := IsAlgClosed.lift
  refine ⟨(IntermediateField.adjoin L0 Z).toSubfield, φ.toRingHom,
    fun x => (IntermediateField.adjoin L0 Z).algebraMap_mem x,
    fun z hz => IntermediateField.subset_adjoin L0 Z hz, ?_⟩
  intro x hx
  have h : (⟨s x, hx⟩ : IntermediateField.adjoin L0 Z) = algebraMap L0 _ x := rfl
  change φ ⟨s x, hx⟩ = t x
  rw [h, φ.commutes]
  rfl

end GlobalTheory
