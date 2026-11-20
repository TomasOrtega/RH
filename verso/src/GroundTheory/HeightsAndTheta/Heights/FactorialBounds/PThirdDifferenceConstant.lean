import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ThirdDifferenceConstant.step_zero_of_bounded (u v K : ℝ)
    (h : ∀ n : ℕ, |u + n * v| ≤ K) : v = 0 := by
  by_contra hv
  have hv' : 0 < |v| := abs_pos.mpr hv
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + |u|) / |v|)
  have h1 : |(n : ℝ) * v| ≤ K + |u| := by
    have : (n : ℝ) * v = (u + n * v) - u := by ring
    rw [this]
    linarith [abs_sub (u + n * v) u, h n]
  rw [abs_mul, Nat.abs_cast] at h1
  rw [div_lt_iff₀ hv'] at hn
  linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem ThirdDifferenceConstant.proof : ThirdDifferenceConstant.Statement := by
  intro A _ f ⟨C, hC⟩ hf
  have key : ∀ z : A, f z = f 0 := by
    intro z
    have hrec : ∀ n : ℕ, f ((n + 1 + 1) • z) - f ((n + 1) • z) =
        (f ((n + 1) • z) - f (n • z)) + (f (z + z) - 2 * f z + f 0) := by
      intro n
      have h := hf (n • z) z z
      have e1 : (n + 1) • z = n • z + z := succ_nsmul z n
      have e2 : (n + 1 + 1) • z = n • z + z + z := by rw [succ_nsmul, succ_nsmul]
      rw [e2, e1]
      linarith
    have hd : ∀ n : ℕ, f ((n + 1) • z) - f (n • z) =
        (f z - f 0) + n * (f (z + z) - 2 * f z + f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => rw [hrec k, ih]; push_cast; ring
    have hc0 : f (z + z) - 2 * f z + f 0 = 0 := by
      refine ThirdDifferenceConstant.step_zero_of_bounded (f z - f 0) _ (C + C) (fun n => ?_)
      rw [← hd n]
      linarith [abs_sub (f ((n + 1) • z)) (f (n • z)), hC ((n + 1) • z), hC (n • z)]
    have ha : ∀ n : ℕ, f (n • z) = f 0 + n * (f z - f 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have := hd k
        rw [hc0, mul_zero, add_zero] at this
        push_cast
        linarith
    have h0 : f z - f 0 = 0 :=
      ThirdDifferenceConstant.step_zero_of_bounded (f 0) _ C (fun n => by rw [← ha n]; exact hC _)
    linarith
  intro x y
  rw [key x, key y]

end GroundTheory.Heights₂.Heights
