import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDimOfAnnihilatingPolyEigenspaces.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.finite_dim_of_annihilating_poly_eigenspaces : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M), (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 → (∀ v ∈ V, Polynomial.aeval T p v = 0) → (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | exact GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | (intros; apply GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces <;> assumption)
