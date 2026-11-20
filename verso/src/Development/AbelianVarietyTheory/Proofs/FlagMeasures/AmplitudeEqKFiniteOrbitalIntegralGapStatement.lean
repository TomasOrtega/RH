import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AmpOrbGap.ampKF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplitudeEqKFiniteOrbitalIntegralGap.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  first | exact @GlobalTheory.AmpOrbGap.ampKF | exact GlobalTheory.AmpOrbGap.ampKF | (intros; apply GlobalTheory.AmpOrbGap.ampKF <;> assumption)
