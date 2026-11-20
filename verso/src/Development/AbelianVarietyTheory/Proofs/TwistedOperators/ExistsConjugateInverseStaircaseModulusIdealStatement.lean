import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdeal
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsConjugateInverseStaircaseModulusIdeal.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (a b : ℕ), ∃ I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) * I' = 1 ∧ ∀ x : D.host.E, x ∈ I' ↔ star x ∈ P.stA sc ^ a * (P.stAbar sc ^ a)⁻¹ * (((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b * (((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹) := by
  first | exact @GlobalTheory.ConjIdeal.stA_modul_conj_inv | exact GlobalTheory.ConjIdeal.stA_modul_conj_inv | (intros; apply GlobalTheory.ConjIdeal.stA_modul_conj_inv <;> assumption)
