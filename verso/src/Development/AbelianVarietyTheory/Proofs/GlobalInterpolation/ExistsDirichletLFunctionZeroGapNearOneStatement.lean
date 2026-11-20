import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZeroGapNearOne.exists_gap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsDirichletLFunctionZeroGapNearOne.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ), (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 → c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.ZeroGapNearOne.exists_gap | exact GlobalTheory.ZeroGapNearOne.exists_gap | (intros; apply GlobalTheory.ZeroGapNearOne.exists_gap <;> assumption)
