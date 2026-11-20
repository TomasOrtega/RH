import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.Unif

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem locallyQuasiFinite_of_isPullback_surjective :
    ∀ (X Z X' Z' : Scheme.{0}) (φ : X ⟶ Z) (φ' : X' ⟶ Z') (a : X' ⟶ X) (p : Z' ⟶ Z),
      IsPullback a φ' φ p → Surjective p → LocallyOfFiniteType φ → QuasiCompact φ →
      LocallyQuasiFinite φ' → LocallyQuasiFinite φ := by
  intro X Z X' Z' φ φ' a p h hp _ hqc _
  have : QuasiCompact φ' := MorphismProperty.of_isPullback h hqc
  refine LocallyQuasiFinite.of_finite_preimage_singleton φ fun z => ?_
  obtain ⟨z', rfl⟩ := p.surjective z
  refine ((φ'.finite_preimage_singleton z').image a).subset fun x hx => ?_
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := p) x z' hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · change φ' (h.isoPullback.inv w) = z'
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw2]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw1]

end GlobalTheory.Unif
