import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AscRungB.rungB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFourierJacobiToBesselNonvanishingTower.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower : FockTot → PartFixed → RungB := by
  first | exact @GlobalTheory.AscRungB.rungB | exact GlobalTheory.AscRungB.rungB | (intros; apply GlobalTheory.AscRungB.rungB <;> assumption)
