import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjection

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEigenvectorLiftOfSurjection.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.eigenvector_lift_of_surjection : ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'), Function.Surjective f → f ∘ₗ T = S ∘ₗ f → ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  first | exact @GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | exact GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | (intros; apply GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts <;> assumption)
