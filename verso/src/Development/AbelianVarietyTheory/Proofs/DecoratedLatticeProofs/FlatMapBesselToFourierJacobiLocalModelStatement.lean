import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatBFLoc.flatBF_of_laws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFlatMapBesselToFourierJacobiLocalModel.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.flatMap_besselToFourierJacobi_localModel : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  first | exact @GlobalTheory.FlatBFLoc.flatBF_of_laws | exact GlobalTheory.FlatBFLoc.flatBF_of_laws | (intros; apply GlobalTheory.FlatBFLoc.flatBF_of_laws <;> assumption)
