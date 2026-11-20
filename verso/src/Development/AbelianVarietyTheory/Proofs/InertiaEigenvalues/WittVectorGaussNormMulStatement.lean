import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormMul

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.witt_gaussNorm_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorGaussNormMul.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.wittVector_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  first | exact @GlobalTheory.witt_gaussNorm_mul | exact GlobalTheory.witt_gaussNorm_mul | (intros; apply GlobalTheory.witt_gaussNorm_mul <;> assumption)
