import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SnMass.VolN.actM_measurePreserving` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnipotentModelProductActionMeasurePreserving.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unipotentModelProductAction_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (k r : ℕ) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E), (∀ w, gM A γ w ∈ Nset k r) → MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  first | exact @GlobalTheory.SnMass.VolN.actM_measurePreserving | exact GlobalTheory.SnMass.VolN.actM_measurePreserving | (intros; apply GlobalTheory.SnMass.VolN.actM_measurePreserving <;> assumption)
