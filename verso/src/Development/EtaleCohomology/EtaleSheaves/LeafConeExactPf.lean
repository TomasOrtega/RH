import Development.EtaleCohomology.EtaleSheaves.LeafDiagCut

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafConeExactPf

section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K L M : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)

/- English proof (translation)
Rewrite using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Use `⟨n.negOnePow • (mappingCone.inl φ).comp c.1 (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[δ_units_smul, δ_comp _ _ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]`. Simplify using `only [Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add, mappingCone.δ_inl, smul_smul, Int.units_mul_self, one_smul]`. Apply `Cochain.ext` to reduce the goal to its premises.

Introduce `p q hpq`. Simplify using `[zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]`.
-/
theorem pre_inr_eq_zero (c : Cocycle (mappingCone φ) M n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom φ) (zcomp (Cocycle.ofHom (mappingCone.inr φ)) c (zero_add n))
      (zero_add n)) = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl φ).comp c.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, zero_add, mappingCone.δ_inl, smul_smul,
    Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro p q hpq
  simp [zcomp, Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq]

end General

end LateralTheory.E.LeafConeExactPf
