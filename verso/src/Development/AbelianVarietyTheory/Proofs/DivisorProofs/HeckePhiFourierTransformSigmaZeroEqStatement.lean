import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformSigmaZeroEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open Complex GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckePhiFourierTransformSigmaZeroEq.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq <;> assumption)
