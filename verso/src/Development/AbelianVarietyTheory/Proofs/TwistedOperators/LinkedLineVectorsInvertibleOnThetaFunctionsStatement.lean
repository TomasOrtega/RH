import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineVectorsInvertibleOnThetaFunctions
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LinkInvTheta.link_inv_theta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLinkedLineVectorsInvertibleOnThetaFunctions.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (L L' S : HSp D) (ζ : Fin L.rank → D.host.E) (ζ' : Fin L'.rank → D.host.E), IsLineVec L ζ → IsLineVec L' ζ' → ∀ l : Lnk L ζ L' ζ', l.τᴴ ⬝ (L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram ∧ ∀ Φ₀, IsThetaFunO ψ S L' Φ₀ → ∃ Ξ, IsThetaFunO ψ L S Ξ ∧ Φ₀ = fun w => star (Ξ (l.κ S w)) := by
  first | exact @GlobalTheory.LinkInvTheta.link_inv_theta | exact GlobalTheory.LinkInvTheta.link_inv_theta | (intros; apply GlobalTheory.LinkInvTheta.link_inv_theta <;> assumption)
