import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianPosSemidefOfLeviFormNonneg
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComplexHessianPosSemidefOfLeviFormNonneg.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg : ∀ (n : ℕ) (φ : V n → ℝ) (z : V n), ContDiffAt ℝ 2 φ z → (∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  first | exact @GlobalTheory.cHess_posSemidef_of_levi_nonneg | exact GlobalTheory.cHess_posSemidef_of_levi_nonneg | (intros; apply GlobalTheory.cHess_posSemidef_of_levi_nonneg <;> assumption)
