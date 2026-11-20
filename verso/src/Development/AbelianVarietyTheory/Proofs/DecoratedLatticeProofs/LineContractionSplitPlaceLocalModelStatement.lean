import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLineContractionSplitPlaceLocalModel.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.lineContraction_splitPlace_localModel : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  first | exact @GlobalTheory.ContrLocProof.contrLoc | exact GlobalTheory.ContrLocProof.contrLoc | (intros; apply GlobalTheory.ContrLocProof.contrLoc <;> assumption)
