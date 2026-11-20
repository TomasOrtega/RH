import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

/- English proof (translation)
Introduce `N lam s hs hbd`. Take `⟨μ, hμ⟩` from `hB N`. Establish `hprob` using `hμ.1`. Establish `hae` using `hμ.2.1`. Rewrite using `[hC N lam μ hμ s hs]`.

Establish `hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Apply `integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)` to reduce the goal to its premises. Use `filter_upwards [hae] with x hx`. Conclude with `pow_le_one₀ (norm_nonneg _) (hbd x hx)`.

Use `_ = 1 := by simp`. Conclude with `mul_le_of_le_one_right (Nat.cast_nonneg _) hint`.
-/
theorem schurFock_of_steps (hB : HaarU) (hC : SchurOrth) : PI.SchurFock := by
  intro N lam s hs hbd
  obtain ⟨μ, hμ⟩ := hB N
  have hprob := hμ.1
  have hae := hμ.2.1
  rw [hC N lam μ hμ s hs]
  have hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1 := by
    calc ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)
          filter_upwards [hae] with x hx
          exact pow_le_one₀ (norm_nonneg _) (hbd x hx)
      _ = 1 := by simp
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hint

end PI.WSF
