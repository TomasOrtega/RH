import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RapidDecay.cuspRapidDecay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FCuspFormsRapidDecay.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.cusp_forms_rapid_decay : GlobalTheory.Published.CuspRapidDecay := by
  first | exact @GlobalTheory.RapidDecay.cuspRapidDecay | exact GlobalTheory.RapidDecay.cuspRapidDecay | (intros; apply GlobalTheory.RapidDecay.cuspRapidDecay <;> assumption)
