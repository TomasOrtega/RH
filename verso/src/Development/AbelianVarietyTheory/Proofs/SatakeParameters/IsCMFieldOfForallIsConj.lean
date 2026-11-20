import Mathlib

open NumberField NumberField.ComplexEmbedding

namespace GlobalTheory.CMFieldCriterion

/- English proof (translation)
Use `⟨fun w => ?_⟩` and prove the remaining obligations. Take `⟨W, rfl⟩` from `w.comap_surjective (K := K)`. Simplify using `only`. Rewrite using `[← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Establish `hx : σ (x : K) = x` using `(IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)`. Establish `h` using `(hσ W.embedding).eq (x : K)`. Rewrite `h` using `[hx]`. Rewrite using `[conjugate_coe_eq]`. Conclude with `h.symm`.
-/
theorem isTotallyReal_fixedField (K : Type) [Field K] [NumberField K] {σ : Gal(K/ℚ)}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsTotallyReal (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
  dsimp only
  rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
    ComplexEmbedding.isReal_iff]
  ext x
  have hx : σ (x : K) = x :=
    (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)
  have h := (hσ W.embedding).eq (x : K)
  rw [hx] at h
  rw [conjugate_coe_eq]
  exact h.symm

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hne : σ ≠ 1` using `(isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)`. Establish `hcard : Nat.card (Subgroup.zpowers σ) = 2`. Rewrite using `[Nat.card_zpowers]`. Use `orderOf_eq_prime ?_ hne` and prove the remaining obligations.

Use extensionality with `x`. Rewrite using `[pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]`. Conclude with `isConj_apply_apply (hσ φ) x`. Establish `hreal` using `isTotallyReal_fixedField K hσ`. Establish `hquad : Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K` using `{ finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }`.

Conclude with `IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K`.
-/
theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    {σ : Gal(K/ℚ)} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : σ ≠ 1 :=
    (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hne
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact isConj_apply_apply (hσ φ) x
  have hreal := isTotallyReal_fixedField K hσ
  have hquad :
      Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K :=
    { finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }
  exact IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K

end GlobalTheory.CMFieldCriterion
