import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPla
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFractionalIdealCompletionDivConjModulusOffBadPla.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ModBarOff.idV_mul_modulBar_inv | exact GlobalTheory.ModBarOff.idV_mul_modulBar_inv | (intros; apply GlobalTheory.ModBarOff.idV_mul_modulBar_inv <;> assumption)
