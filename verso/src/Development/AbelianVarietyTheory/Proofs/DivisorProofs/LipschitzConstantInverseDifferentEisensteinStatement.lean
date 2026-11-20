import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzConstantInverseDifferentEisenstein
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLipschitzConstantInverseDifferentEisenstein.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  first | exact @GlobalTheory.LipEisConst.lip_const_eis | exact GlobalTheory.LipEisConst.lip_const_eis | (intros; apply GlobalTheory.LipEisConst.lip_const_eis <;> assumption)
