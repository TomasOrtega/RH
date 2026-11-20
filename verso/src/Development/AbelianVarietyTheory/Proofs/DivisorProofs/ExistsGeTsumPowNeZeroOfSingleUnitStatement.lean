import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeTsumPowNeZeroOfSingleUnit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGeTsumPowNeZeroOfSingleUnit.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_ge_tsum_pow_ne_zero_of_single_unit : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  first | exact @GlobalTheory.tsum_pow_eventually_ne_zero | exact GlobalTheory.tsum_pow_eventually_ne_zero | (intros; apply GlobalTheory.tsum_pow_eventually_ne_zero <;> assumption)
