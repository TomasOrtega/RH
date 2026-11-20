import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionMulModulusOffExceptiona
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChiGrid.Places.idV_mul_modul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFractionalIdealCompletionMulModulusOffExceptiona.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.fractionalIdealCompletion_mul_modulus_offExceptional : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (v : GlobalTheory.FinPl.Pl D), v ∉ P.S0 → ∀ 𝔞 : GlobalTheory.SeeSaw.FI D, GlobalTheory.SeeSaw.idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v ∧ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) v = GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ChiGrid.Places.idV_mul_modul | exact GlobalTheory.ChiGrid.Places.idV_mul_modul | (intros; apply GlobalTheory.ChiGrid.Places.idV_mul_modul <;> assumption)
