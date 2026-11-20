import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLe
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZeroCells.ncard_cells_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FNcardUnitCellsDirichletLZerosNearOneLe.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  first | exact @GlobalTheory.ZeroCells.ncard_cells_le | exact GlobalTheory.ZeroCells.ncard_cells_le | (intros; apply GlobalTheory.ZeroCells.ncard_cells_le <;> assumption)
