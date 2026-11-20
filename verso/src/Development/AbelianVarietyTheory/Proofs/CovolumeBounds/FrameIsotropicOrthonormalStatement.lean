import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCovolumeBounds%2FFrameIsotropicOrthonormal.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.frame_isotropic_orthonormal : ∀ k r : ℕ, 1 ≤ k → (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  first | exact @GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | exact GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | (intros; apply GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic <;> assumption)
