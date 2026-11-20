import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormInverseDifferentIdealPowEqDiscr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAbsNormInverseDifferentIdealPowEqDiscr.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  first | exact @GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | exact GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv | (intros; apply GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv <;> assumption)
