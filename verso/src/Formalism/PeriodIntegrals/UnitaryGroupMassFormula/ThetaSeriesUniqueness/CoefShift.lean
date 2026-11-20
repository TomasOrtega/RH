import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete

noncomputable section

namespace PI.SSU

open Complex

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem coef_shift (hS : ShiftInv) (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ) (hf : Differentiable ℂ f)
    (h1 : ∀ u, f (u + 1) = f u)
    (hτ : ∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) (n : ℤ) :
    coef f n = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * τ)) * coef f (n + k) := by
  rw [← hS f hf h1 τ n, ← hS f hf h1 0 (n + k), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [hτ, add_zero]
  have e : cexp (-(2 * (Real.pi : ℂ) * I * k * x)) * cexp (-(2 * (Real.pi : ℂ) * I * n * (x + τ))) =
      cexp (-(2 * (Real.pi : ℂ) * I * n * τ)) * cexp (-(2 * (Real.pi : ℂ) * I * ((n + k : ℤ) : ℂ) * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (K * f x) * e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem key_of (hS : ShiftInv) (hC : Complete) : KeyP := by
  intro f τ K k hf hK hk h1 hτ h0
  apply hC f hf h1
  have hrel : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + k) = 0 := by
    intro n
    rw [coef_shift hS f τ K k hf h1 hτ n, mul_eq_zero,
      or_iff_right (mul_ne_zero hK (Complex.exp_ne_zero _))]
  have H : ∀ n : ℤ, coef f n = 0 ↔ coef f (n + 1) = 0 := by
    intro n
    rcases hk with rfl | rfl
    · exact hrel n
    · have := hrel (n + 1)
      rw [show n + 1 + -1 = n by ring] at this
      exact this.symm
  intro n
  induction n using Int.induction_on with
  | zero => exact h0
  | succ i hi => exact (H i).mp hi
  | pred i hi =>
    have := H (-(i:ℤ) - 1)
    rw [show -(i:ℤ) - 1 + 1 = -i by ring] at this
    exact this.mpr hi

end PI.SSU
