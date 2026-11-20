import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRung
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AscBottom.rung0` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNonvanishingThetaTowerBottomRung.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.nonvanishing_thetaTower_bottom_rung : FockTot → Rung0 := by
  first | exact @GlobalTheory.AscBottom.rung0 | exact GlobalTheory.AscBottom.rung0 | (intros; apply GlobalTheory.AscBottom.rung0 <;> assumption)
