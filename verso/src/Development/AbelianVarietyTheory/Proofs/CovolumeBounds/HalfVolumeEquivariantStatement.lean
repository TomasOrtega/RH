import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.HalfVolumeEquivariant
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCovolumeBounds%2FHalfVolumeEquivariant.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.half_volume_equivariant : ∀ k r : ℕ, 1 ≤ k → (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧ ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  first | exact @GlobalTheory.HCXi.vHalf_left_inv_and_mul | exact GlobalTheory.HCXi.vHalf_left_inv_and_mul | (intros; apply GlobalTheory.HCXi.vHalf_left_inv_and_mul <;> assumption)
