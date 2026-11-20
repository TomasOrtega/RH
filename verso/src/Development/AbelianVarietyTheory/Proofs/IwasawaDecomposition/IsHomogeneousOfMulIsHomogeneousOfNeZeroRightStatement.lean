import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsHomogeneousOfMulIsHomogeneousOfNeZeroRight.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a := by
  first | exact @GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | exact GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | (intros; apply GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right <;> assumption)
