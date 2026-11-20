import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FStableGoodFormsMeetGenericType.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.stableGoodForms_meet_generic_type : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7), NExpTied D → GrpSide D → MeetsAll D := by
  first | exact @GlobalTheory.TwInputs.meetsAll_of_ties | exact GlobalTheory.TwInputs.meetsAll_of_ties | (intros; apply GlobalTheory.TwInputs.meetsAll_of_ties <;> assumption)
