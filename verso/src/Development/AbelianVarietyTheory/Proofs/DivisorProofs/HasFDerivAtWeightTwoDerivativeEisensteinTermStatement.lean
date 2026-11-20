import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasFDerivAtWeightTwoDerivativeEisensteinTerm.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x) (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j + (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  first | exact @GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | exact GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm | (intros; apply GlobalTheory.WeightTwoSum.hasFDerivAt_eTerm <;> assumption)
