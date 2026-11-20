import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumLambertDoubleSeriesDivisors
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WpFam.hasSum_lambert` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasSumLambertDoubleSeriesDivisors.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.hasSum_lambert_double_series_divisors : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  first | exact @GlobalTheory.WpFam.hasSum_lambert | exact GlobalTheory.WpFam.hasSum_lambert | (intros; apply GlobalTheory.WpFam.hasSum_lambert <;> assumption)
