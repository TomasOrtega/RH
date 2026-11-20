import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStandardAuxiliaryFramesAllRowGrids
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsStandardAuxiliaryFramesAllRowGrids.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_standardAuxiliaryFrames_allRowGrids : All fun {_} _ _ _ {G} _ _ => ∃ F : Frames G, Std F := by
  first | exact @GlobalTheory.AscFin.exists_std_frames | exact GlobalTheory.AscFin.exists_std_frames | (intros; apply GlobalTheory.AscFin.exists_std_frames <;> assumption)
