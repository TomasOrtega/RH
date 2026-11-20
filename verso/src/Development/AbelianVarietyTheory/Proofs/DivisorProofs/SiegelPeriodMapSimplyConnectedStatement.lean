import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnected
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelPeriodMapSimplyConnected.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.siegel_period_map_simply_connected : ∀ g : ℕ, IsPeriodMap (siegel g) tauU ∧ SimplyConnectedSpace (siegel g) := by
  first | exact @GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected | exact GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected | (intros; apply GlobalTheory.SiegelOpen.isPeriodMap_tauU_and_simplyConnected <;> assumption)
