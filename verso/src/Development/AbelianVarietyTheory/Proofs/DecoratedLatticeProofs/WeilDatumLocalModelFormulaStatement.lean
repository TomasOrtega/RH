import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocOm.omLoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FWeilDatumLocalModelFormula.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.weilDatum_localModel_formula : ∀ (D : D7), OmLoc D := by
  first | exact @GlobalTheory.LocOm.omLoc | exact GlobalTheory.LocOm.omLoc | (intros; apply GlobalTheory.LocOm.omLoc <;> assumption)
