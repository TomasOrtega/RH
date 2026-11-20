import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesGoodRowGrids
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AscFin.GoodStd.std_good` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FStandardAuxiliaryFramesGoodRowGrids.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.standardAuxiliaryFrames_good_row_grids : GlobalTheory.SepRows.DepFixed → All fun {_} _ _ _ {G} W _ => ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Good v W (lineLat F) := by
  first | exact @GlobalTheory.AscFin.GoodStd.std_good | exact GlobalTheory.AscFin.GoodStd.std_good | (intros; apply GlobalTheory.AscFin.GoodStd.std_good <;> assumption)
