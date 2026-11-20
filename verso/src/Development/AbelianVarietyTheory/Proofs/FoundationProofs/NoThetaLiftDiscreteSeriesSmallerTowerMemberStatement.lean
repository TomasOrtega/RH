import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoThetaLiftDiscreteSeriesSmallerTowerMember
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNoThetaLiftDiscreteSeriesSmallerTowerMember.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.no_thetaLift_discreteSeries_smaller_tower_member : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFourth X := by
  first | exact @GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner | exact GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner | (intros; apply GlobalTheory.TowerDrop.archimedeanRallisFourth_of_discreteSeriesBlattner <;> assumption)
