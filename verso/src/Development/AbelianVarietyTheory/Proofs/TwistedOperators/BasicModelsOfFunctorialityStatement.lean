import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasicModelsOfFunctoriality
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepRows.coreModels` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBasicModelsOfFunctoriality.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.basic_models_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → CoreModels := by
  first | exact @GlobalTheory.SepRows.coreModels | exact GlobalTheory.SepRows.coreModels | (intros; apply GlobalTheory.SepRows.coreModels <;> assumption)
