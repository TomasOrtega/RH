import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibreExp.exists_exp_lattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsComplexFibreExponentialFullLattice.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_complexFibreExponential_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.FibreExp.exists_exp_lattice | exact GlobalTheory.FibreExp.exists_exp_lattice | (intros; apply GlobalTheory.FibreExp.exists_exp_lattice <;> assumption)
