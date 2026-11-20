import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOuterZetaIntegrand
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousOuterZetaIntegrand.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.continuous_outer_zeta_integrand : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ),
  Continuous W₀ → Continuous W' → Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) →
  Continuous (Aq ψ W₀ W' Φ s) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Unfolding.AqCont.continuous_Aq | exact GlobalTheory.CompanionTheory.GL2Unfolding.AqCont.continuous_Aq | (intros; apply GlobalTheory.CompanionTheory.GL2Unfolding.AqCont.continuous_Aq <;> assumption)
