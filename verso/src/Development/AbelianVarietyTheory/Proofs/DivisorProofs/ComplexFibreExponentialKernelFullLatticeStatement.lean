import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExpKernel.kernel_isFullLattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComplexFibreExponentialKernelFullLattice.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.complexFibreExponential_kernel_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.ExpKernel.kernel_isFullLattice | exact GlobalTheory.ExpKernel.kernel_isFullLattice | (intros; apply GlobalTheory.ExpKernel.kernel_isFullLattice <;> assumption)
