import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplifierOfHypotheses.lean&line=445#L445)
-/
theorem _root_.GlobalTheory.T.amplifier_of_hypotheses : BranchingSupport.Hyps → GlobalTheory.CellAmp.AmpKF := by
  first | exact @GlobalTheory.AmpOrb.ampKF | exact GlobalTheory.AmpOrb.ampKF | (intros; apply GlobalTheory.AmpOrb.ampKF <;> assumption)
