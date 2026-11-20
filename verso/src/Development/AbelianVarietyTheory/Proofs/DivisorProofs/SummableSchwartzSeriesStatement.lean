import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzSeries
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSummableSchwartzSeries.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.summable_schwartz_series : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  first | exact @GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | exact GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms | (intros; apply GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms <;> assumption)
