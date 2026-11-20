import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FDecayThresholdsOfSpectralGapCondition.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.decayThresholds_of_spectralGapCondition : ∀ (k r : ℕ) (h : ℝ), GapOK k r h → JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  first | exact @GlobalTheory.thresholds_of_gapOK | exact GlobalTheory.thresholds_of_gapOK | (intros; apply GlobalTheory.thresholds_of_gapOK <;> assumption)
