import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSinhcAdMulVecOfAdSqEigen.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ), (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | exact GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | (intros; apply GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen <;> assumption)
