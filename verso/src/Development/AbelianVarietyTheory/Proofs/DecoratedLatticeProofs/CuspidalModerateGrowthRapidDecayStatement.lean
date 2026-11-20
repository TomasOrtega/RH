import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeo.cuspDecayBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FCuspidalModerateGrowthRapidDecay.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay : GlobalTheory.Published.CuspDecayBound := by
  first | exact @GlobalTheory.CuspGeo.cuspDecayBound | exact GlobalTheory.CuspGeo.cuspDecayBound | (intros; apply GlobalTheory.CuspGeo.cuspDecayBound <;> assumption)
