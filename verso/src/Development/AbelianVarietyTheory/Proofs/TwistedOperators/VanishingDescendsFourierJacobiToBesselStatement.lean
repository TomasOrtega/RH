import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBessel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FVanishingDescendsFourierJacobiToBessel.lean&line=237#L237)
-/
theorem _root_.GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel : ∀ D : D7, VanFB D := by
  first | exact @GlobalTheory.Asc.VanJac.vanFB | exact GlobalTheory.Asc.VanJac.vanFB | (intros; apply GlobalTheory.Asc.VanJac.vanFB <;> assumption)
