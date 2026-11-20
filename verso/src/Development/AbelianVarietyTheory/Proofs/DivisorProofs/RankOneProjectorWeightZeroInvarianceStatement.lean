import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)
