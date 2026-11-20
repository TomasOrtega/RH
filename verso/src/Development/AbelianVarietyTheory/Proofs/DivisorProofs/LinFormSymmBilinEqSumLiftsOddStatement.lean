import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLinFormSymmBilinEqSumLiftsOdd.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_lifts <;> assumption)
