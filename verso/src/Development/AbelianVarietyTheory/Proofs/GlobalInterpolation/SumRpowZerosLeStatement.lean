import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRpowZerosLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSumRpowZerosLe.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.exists_sum_characters_finsum_zeros_rpow_re_sub_one_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  first | exact @GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le | exact GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le | (intros; apply GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le <;> assumption)
