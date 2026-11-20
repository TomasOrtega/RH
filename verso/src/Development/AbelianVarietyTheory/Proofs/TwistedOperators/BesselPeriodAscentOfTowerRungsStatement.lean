import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Asc.ascent_of_rungs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBesselPeriodAscentOfTowerRungs.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.besselPeriod_ascent_of_tower_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_rungs | exact GlobalTheory.Asc.ascent_of_rungs | (intros; apply GlobalTheory.Asc.ascent_of_rungs <;> assumption)
