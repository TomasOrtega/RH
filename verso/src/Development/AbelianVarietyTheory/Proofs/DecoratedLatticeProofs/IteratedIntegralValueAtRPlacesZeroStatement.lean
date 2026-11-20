import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueAtRPlacesZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIteratedIntegralValueAtRPlacesZero.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.iteratedIntegralValueAtRPlaces_zero : ∀ D : D7, ValQr D 0 := by
  first | exact @GlobalTheory.QVal.valQr_zero | exact GlobalTheory.QVal.valQr_zero | (intros; apply GlobalTheory.QVal.valQr_zero <;> assumption)
