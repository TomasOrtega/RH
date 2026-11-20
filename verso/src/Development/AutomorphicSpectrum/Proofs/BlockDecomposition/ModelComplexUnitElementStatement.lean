import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PerfVB.unit_of_model` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FModelComplexUnitElement.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.model_complex_unit_element : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.unit_of_model | exact GlobalTheory.CompanionTheory.PerfVB.unit_of_model | (intros; apply GlobalTheory.CompanionTheory.PerfVB.unit_of_model <;> assumption)
