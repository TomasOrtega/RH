import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LastKerLoc.lastLoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSplitPlaceDoubleStepKernelLocalModels.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_kernel_localModels : ∀ (D : D7), LastLoc D := by
  first | exact @GlobalTheory.LastKerLoc.lastLoc | exact GlobalTheory.LastKerLoc.lastLoc | (intros; apply GlobalTheory.LastKerLoc.lastLoc <;> assumption)
