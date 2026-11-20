import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h0 : algebraMap O (FractionRing O) ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero`. Use `⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]`.
-/
theorem KO_divisible_by_uniformiser : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]

end GlobalTheory
