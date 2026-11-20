import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Asc.ascent_of_depFixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBesselPeriodNonvanishingAscentOfDepthData.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data : DepFixed → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_depFixed | exact GlobalTheory.Asc.ascent_of_depFixed | (intros; apply GlobalTheory.Asc.ascent_of_depFixed <;> assumption)
