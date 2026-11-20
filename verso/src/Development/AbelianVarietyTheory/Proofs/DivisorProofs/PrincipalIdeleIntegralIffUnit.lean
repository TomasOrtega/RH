import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.RatIdInt

/- English proof (translation)
Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Prove the first alternative. A detailed English derivation is pending.
-/
theorem mem_RInt_iff_isIntegral (L : Type) [Field L] [NumberField L] (x : L) :
    (x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ RInt ℚ L ↔ IsIntegral ℤ x := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv ℚ L
  constructor
  · intro hx
    have hv := (h2 _).1 hx
    rw [h1] at hv
    have hr : x ∈ (algebraMap (𝓞 L) L).range := by
      apply HeightOneSpectrum.mem_integers_of_valuation_le_one
      intro P
      have := hv P
      rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    obtain ⟨y, rfl⟩ := hr
    exact RingOfIntegers.isIntegral_coe y
  · intro hx
    apply Subring.subset_closure
    exact Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ratId_mem_intU_iff : ∀ (L : Type) [Field L] [NumberField L] (a : Lˣ),
    ratId ℚ L a ∈ intU ℚ L ↔ IsIntegral ℤ (a : L) ∧ IsIntegral ℤ ((a⁻¹ : Lˣ) : L) := by
  intro L _ _ a
  rw [intU, Submonoid.mem_units_iff, ← map_inv]
  exact and_congr (mem_RInt_iff_isIntegral L (a : L)) (mem_RInt_iff_isIntegral L ((a⁻¹ : Lˣ) : L))

end GlobalTheory.RatIdInt
