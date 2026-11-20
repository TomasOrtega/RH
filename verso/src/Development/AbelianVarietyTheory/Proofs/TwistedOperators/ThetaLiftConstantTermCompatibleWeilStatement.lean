import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftConstantTermCompatibleWeil
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaLiftConstantTermCompatibleWeil.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.thetaLift_constantTerm_compatibleWeil : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTermOfCompatible D := by
  first | exact @GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | exact GlobalTheory.TowerCT.towerConstTermOfCompatible_holds | (intros; apply GlobalTheory.TowerCT.towerConstTermOfCompatible_holds <;> assumption)
