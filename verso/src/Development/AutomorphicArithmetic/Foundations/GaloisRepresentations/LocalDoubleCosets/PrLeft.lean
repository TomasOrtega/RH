import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `G _ _ _ _ _ _ B hB _ _ μ _ χ b`. Use `haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _`. Take `⟨c', hc'⟩ : ∃ c' : NNReal, map (· * b) μ = c' • μ` from `⟨_, isMulLeftInvariant_eq_smul _ _⟩`. Use `⟨(((χ b)⁻¹ : ℂˣ) : ℂ) * ((c' : ℝ) : ℂ), fun f g => ?_⟩` and prove the remaining obligations.

Use `set H : B → ℂ := fun y => (χ y : ℂ) * f ((y : G)⁻¹ * g) with hH`. Establish `key : pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g = (((χ b)⁻¹ : ℂˣ) : ℂ) * ∫ x, H (x * b) ∂μ`. Unfold `pr`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [hH, map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]`. Rewrite using `[Units.val_inv_eq_inv_val]`. Clear denominators, using `[(χ b).ne_zero]` for the nonvanishing conditions. Establish `e` using `(MeasurableEquiv.mulRight b).measurableEmbedding.integral_map (μ := μ) H`.

Rewrite `e` using `[MeasurableEquiv.coe_mulRight]`. Rewrite using `[key, ← e, hc', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Establish `: pr B μ χ f g = ∫ x, H x ∂μ` using `rfl`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prLeft : PrLeft := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ b
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c', hc'⟩ : ∃ c' : NNReal, map (· * b) μ = c' • μ :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨(((χ b)⁻¹ : ℂˣ) : ℂ) * ((c' : ℝ) : ℂ), fun f g => ?_⟩
  set H : B → ℂ := fun y => (χ y : ℂ) * f ((y : G)⁻¹ * g) with hH
  have key : pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g
      = (((χ b)⁻¹ : ℂˣ) : ℂ) * ∫ x, H (x * b) ∂μ := by
    unfold pr
    rw [← integral_const_mul]
    congr 1
    ext x
    simp only [hH, map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    rw [Units.val_inv_eq_inv_val]
    field_simp [(χ b).ne_zero]
  have e := (MeasurableEquiv.mulRight b).measurableEmbedding.integral_map (μ := μ) H
  rw [MeasurableEquiv.coe_mulRight] at e
  rw [key, ← e, hc', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : pr B μ χ f g = ∫ x, H x ∂μ := rfl
  rw [this]
  ring

end UpperTheory.Gal.LocD

end
