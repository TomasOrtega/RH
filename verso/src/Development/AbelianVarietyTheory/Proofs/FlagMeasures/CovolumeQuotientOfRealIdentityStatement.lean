import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeQuotientOfRealIdentity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.covolQuotient_arith` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCovolumeQuotientOfRealIdentity.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.covolumeQuotient_ofReal_identity : ∀ (d c : ℝ) (f t : ℕ) (m : ℝ≥0∞), 1 ≤ d → 0 < c → ENNReal.ofReal (((d ^ 2) ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ f * Real.sqrt (d ^ 2)) = ENNReal.ofReal ((d ^ (2 * t))⁻¹ * (2⁻¹ : ℝ) ^ 0 * Real.sqrt d) * m → ENNReal.ofReal ((2 * c) ^ f) * m = ENNReal.ofReal (d ^ (1 / 2 - 2 * (t : ℝ)) * c ^ f) := by
  first | exact @GlobalTheory.covolQuotient_arith | exact GlobalTheory.covolQuotient_arith | (intros; apply GlobalTheory.covolQuotient_arith <;> assumption)
