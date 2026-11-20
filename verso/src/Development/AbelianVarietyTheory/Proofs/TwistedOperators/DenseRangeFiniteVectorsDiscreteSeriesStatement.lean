import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseRangeFiniteVectorsDiscreteSeries
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AnalyticDense.dense_range_of_factorial_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDenseRangeFiniteVectorsDiscreteSeries.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.dense_range_finite_vectors_discrete_series : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T), Nontrivial D.HK.V → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → Dense (Set.range D.ι) := by
  first | exact @GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | exact GlobalTheory.AnalyticDense.dense_range_of_factorial_bound | (intros; apply GlobalTheory.AnalyticDense.dense_range_of_factorial_bound <;> assumption)
