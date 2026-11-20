import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitMulSqQuadraticDefectStep
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsUnitMulSqQuadraticDefectStep.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_unit_mul_sq_quadratic_defect_step : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (δ π : K) (k : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) → w δ = 1 → w 4 < w (δ - 1) → w (δ - 1) = WithZero.exp (-(2 * (k : ℤ))) → ∃ c : K, w c = 1 ∧ w (δ * c ^ 2 - 1) < w (δ - 1) := by
  first | exact @GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt | exact GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt | (intros; apply GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt <;> assumption)
