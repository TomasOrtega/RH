import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnDbarCoefficients
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffOnDbarCoefficients.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.contDiffOn_dbar_coefficients : ∀ {n : ℕ} {γ : V n → Alt n} {U : Set (V n)}, IsOpen U → (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) → ∀ (T : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  first | exact @GlobalTheory.CxForm.contDiffOn_repr_dbarAt | exact GlobalTheory.CxForm.contDiffOn_repr_dbarAt | (intros; apply GlobalTheory.CxForm.contDiffOn_repr_dbarAt <;> assumption)
