import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCyclicWordMarkedClustersOfAtMostTwoInWindow.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n → WindowTwo th L → Clusters th j := by
  first | exact @GlobalTheory.HTW.winClusters | exact GlobalTheory.HTW.winClusters | (intros; apply GlobalTheory.HTW.winClusters <;> assumption)
