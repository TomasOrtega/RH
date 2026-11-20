import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAntiholomorphicDbarChernFormOfGramMatrixEqZero.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | exact GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt <;> assumption)
