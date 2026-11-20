import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplyConnectedCover
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSimplyConnectedCover.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.simply_connected_cover : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}, SimplyConnectedSpace B → SimplyConnectedSpace (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.cov B g) := by
  first | exact @GlobalTheory.simplyConnected_cov | exact GlobalTheory.simplyConnected_cov | (intros; apply GlobalTheory.simplyConnected_cov <;> assumption)
