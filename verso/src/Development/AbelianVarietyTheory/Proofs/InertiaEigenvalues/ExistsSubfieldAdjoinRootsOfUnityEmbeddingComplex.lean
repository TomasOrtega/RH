import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra L0 K := s.toAlgebra`. Use `letI : Algebra L0 ℂ := t.toAlgebra`. Establish `hint : ∀ z ∈ Z, IsIntegral L0 z`. Introduce `z hz`. Take `⟨n, hn, hzn⟩` from `hZ z hz`.

Conclude with `⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hzn]⟩`. Use `haveI : Algebra.IsAlgebraic L0 (IntermediateField.adjoin L0 Z) := IntermediateField.isAlgebraic_adjoin hint`. Set `φ : IntermediateField.adjoin L0 Z →ₐ[L0] ℂ` to `IsAlgClosed.lift`. Use `⟨(IntermediateField.adjoin L0 Z).toSubfield, φ.toRingHom, fun x => (IntermediateField.adjoin L0 Z).algebraMap_mem x, fun z hz => IntermediateField.subset_adjoin L0 Z hz, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `h : (⟨s x, hx⟩ : IntermediateField.adjoin L0 Z) = algebraMap L0 _ x` using `rfl`. Express the relevant statement in the definitionally equal form `φ ⟨s x, hx⟩ = t x`. Rewrite using `[h, φ.commutes]`. Both sides reduce to the same expression.
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
