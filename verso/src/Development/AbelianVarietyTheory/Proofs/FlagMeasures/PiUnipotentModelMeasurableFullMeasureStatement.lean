import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPiUnipotentModelMeasurableFullMeasure.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.pi_unipotentModel_measurable_full_measure : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.pi_nset_full | exact GlobalTheory.SnMass.VolN.pi_nset_full | (intros; apply GlobalTheory.SnMass.VolN.pi_nset_full <;> assumption)
