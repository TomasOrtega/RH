import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.gram_leading_minor_lower_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FGramLeadingMinorLowerBoundIntegral.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.gram_leading_minor_lower_bound_integral : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  first | exact @GlobalTheory.ClassFin.gram_leading_minor_lower_bound | exact GlobalTheory.ClassFin.gram_leading_minor_lower_bound | (intros; apply GlobalTheory.ClassFin.gram_leading_minor_lower_bound <;> assumption)
