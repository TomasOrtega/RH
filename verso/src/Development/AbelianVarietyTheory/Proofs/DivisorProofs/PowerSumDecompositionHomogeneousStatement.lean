import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumDecompositionHomogeneous
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPowerSumDecompositionHomogeneous.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.power_sum_decomposition_homogeneous : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Pol ι N), F.IsHomogeneous (dimFl ι N + 1) → ∃ Q : ι → ℕ → Pol ι N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl ι N + 1 - k)) ∧ F = ∑ τ : ι, ∑ k ∈ Finset.Icc 1 N, pSum τ k * Q τ k := by
  first | exact @GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous | exact GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous | (intros; apply GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous <;> assumption)
