import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralStabilizes
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilSB.ballIntegral_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormFormBallIntegralStabilizes.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.norm_form_ball_integral_stabilizes : (ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∃ (c : ℂ) (n₀ : ℤ), ∀ n ≤ n₀,
  ∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = c := by
  first | exact @GlobalTheory.CompanionTheory.WeilSB.ballIntegral_stable | exact GlobalTheory.CompanionTheory.WeilSB.ballIntegral_stable | (intros; apply GlobalTheory.CompanionTheory.WeilSB.ballIntegral_stable <;> assumption)
