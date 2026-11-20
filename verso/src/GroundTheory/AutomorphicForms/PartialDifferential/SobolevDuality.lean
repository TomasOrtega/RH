import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Duality

variable {s : ℝ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_add_lpTwo (f g : Lp ℂ 2 (volume : Measure E)) :
    (star (f + g) : Lp ℂ 2 (volume : Measure E)) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_star f, Lp.coeFn_star g,
    Lp.coeFn_add (star f) (star g), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp only [Pi.star_apply]
  rw [h5, Pi.add_apply, star_add]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem star_smul_lpTwo (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    (star (c • f) : Lp ℂ 2 (volume : Measure E)) = (starRingEnd ℂ c) • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_star f, Lp.coeFn_smul (starRingEnd ℂ c) (star f),
    Lp.coeFn_smul c f] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2]
  simp [h4]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem norm_star_lpTwo (f : Lp ℂ 2 (volume : Measure E)) :
    ‖(star f : Lp ℂ 2 (volume : Measure E))‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact ae_of_all _ fun x ↦ by simp

def dualPairing (v : SobolevSpace E ℂ (-s)) : StrongDual ℂ (SobolevSpace E ℂ s) :=
  (innerSL ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))).comp
    ((SobolevSpace.besselₗᵢ (E := E) (F := ℂ) s) : SobolevSpace E ℂ s →L[ℂ] Lp ℂ 2 (volume : Measure E))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualPairing_apply' (v : SobolevSpace E ℂ (-s)) (u : SobolevSpace E ℂ s) :
    dualPairing v u = inner ℂ (star (SobolevSpace.bessel (-s) v) : Lp ℂ 2 (volume : Measure E))
      (SobolevSpace.bessel s u) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem norm_dualPairing (v : SobolevSpace E ℂ (-s)) : ‖dualPairing (s := s) v‖ = ‖v‖ := by
  rw [dualPairing, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, innerSL_apply_norm,
    norm_star_lpTwo]
  rfl

def dualPairingₗᵢ : SobolevSpace E ℂ (-s) →ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) where
  toFun := dualPairing
  map_add' v w := by
    ext u
    rw [ContinuousLinearMap.add_apply, dualPairing_apply', dualPairing_apply',
      dualPairing_apply', map_add, star_add_lpTwo, inner_add_left]
  map_smul' c v := by
    ext u
    rw [ContinuousLinearMap.smul_apply, dualPairing_apply', dualPairing_apply', map_smul,
      star_smul_lpTwo, inner_smul_left, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]
  norm_map' v := norm_dualPairing v

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dualPairing_surjective :
    Function.Surjective (dualPairing : SobolevSpace E ℂ (-s) → StrongDual ℂ (SobolevSpace E ℂ s)) := by
  intro ℓ
  set L : StrongDual ℂ (Lp ℂ 2 (volume : Measure E)) :=
    ℓ.comp (SobolevSpace.besselₗᵢ s).symm.toLinearIsometry.toContinuousLinearMap
  set y := (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure E))).symm L
  refine ⟨(SobolevSpace.besselₗᵢ (-s)).symm (star y), ?_⟩
  ext u
  have hy : ∀ g, inner ℂ y g = L g := fun g ↦ by
    rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [dualPairing_apply', ← SobolevSpace.besselₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply,
    star_star, hy]
  simp only [L, ContinuousLinearMap.comp_apply]
  rw [← SobolevSpace.besselₗᵢ_apply]
  simp

def dualEquiv : SobolevSpace E ℂ (-s) ≃ₗᵢ[ℂ] StrongDual ℂ (SobolevSpace E ℂ s) :=
  LinearIsometryEquiv.ofSurjective dualPairingₗᵢ dualPairing_surjective

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem dualEquiv_apply (v : SobolevSpace E ℂ (-s)) :
    dualEquiv v = dualPairing v := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem bessel_ofSchwartz (φ : 𝓢(E, ℂ)) :
    SobolevSpace.bessel s (SobolevSpace.ofSchwartz s φ) =
      (SchwartzMap.fourierMultiplierCLM ℂ (weight s) φ).toLp 2 := by
  apply toTemperedDistribution_injective
  simp only
  rw [SobolevSpace.toDistribution_bessel, SobolevSpace.toDistribution_ofSchwartz,
    Lp.toTemperedDistribution_toLp_eq, besselPotential_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (weight_hasTemperateGrowth _)]

end Duality

end

end GroundTheory.Automorphic.Sobolev
