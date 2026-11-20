import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer : RankOne := by
  first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)
