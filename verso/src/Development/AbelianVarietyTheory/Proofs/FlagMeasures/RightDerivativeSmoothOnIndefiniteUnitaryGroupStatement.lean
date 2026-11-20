import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.rdM_smoothOnH` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRightDerivativeSmoothOnIndefiniteUnitaryGroup.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f → ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧ ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  first | exact @GlobalTheory.rdM_smoothOnH | exact GlobalTheory.rdM_smoothOnH | (intros; apply GlobalTheory.rdM_smoothOnH <;> assumption)
