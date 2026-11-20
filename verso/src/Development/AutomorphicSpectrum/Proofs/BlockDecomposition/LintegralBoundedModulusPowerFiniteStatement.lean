import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFinite
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLintegralBoundedModulusPowerFinite.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.lintegral_bounded_modulus_power_finite : ForS fun F _ _ _ _ _ _ _ => ∀ B e : ℝ, 0 < e →
  ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) a ∂multHaar F < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top | exact GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top | (intros; apply GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top <;> assumption)
