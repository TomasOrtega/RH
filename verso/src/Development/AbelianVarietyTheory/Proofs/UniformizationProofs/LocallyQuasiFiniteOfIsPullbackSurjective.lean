import Mathlib

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.Unif

/- English proof (translation)
Introduce `X Z X' Z' φ φ' a p h hp _ hqc _`. Establish `: QuasiCompact φ'` using `MorphismProperty.of_isPullback h hqc`. Use `LocallyQuasiFinite.of_finite_preimage_singleton φ fun z => ?_` and prove the remaining obligations. Take `⟨z', rfl⟩` from `p.surjective z`. Use `((φ'.finite_preimage_singleton z').image a).subset fun x hx => ?_` and prove the remaining obligations.

Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := φ) (g := p) x z' hx`. Use `⟨h.isoPullback.inv w, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ' (h.isoPullback.inv w) = z'`. Rewrite using `[← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw2]`. Rewrite using `[← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw1]`.
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
