import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TowerConstTermObj.towerConstTerm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FConstantTermLiftIsotropicSubspace.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.constantTermLift_isotropicSubspace : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by
  first | exact @GlobalTheory.TowerConstTermObj.towerConstTerm | exact GlobalTheory.TowerConstTermObj.towerConstTerm | (intros; apply GlobalTheory.TowerConstTermObj.towerConstTerm <;> assumption)
