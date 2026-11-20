import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariant
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwasawaIntegralRightTranslateInvariant.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.iwasawa_integral_right_translate_invariant : ForS fun F _ _ _ _ _ _ ψ => ∀ f : GL (Fin 2) F → ENNReal, Measurable f → (∀ x h, f (uni2 x * h) = f h) →
  ∀ g : GL (Fin 2) F, ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p * g) ∂mIw ψ = ∫⁻ p, ENNReal.ofReal (wR p) * f (hI p) ∂mIw ψ := by
  first | exact @GlobalTheory.CompanionTheory.RInvL.main | exact GlobalTheory.CompanionTheory.RInvL.main | (intros; apply GlobalTheory.CompanionTheory.RInvL.main <;> assumption)
