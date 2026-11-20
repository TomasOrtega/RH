import Mathlib

namespace Bl.SecondBlockLemmaN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ (z : Complex),
  (∀ (n : Nat), LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} z n) 1)) (1 / 2)) → Eq.{1} z 1 := by
  intro z h
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hx := h (2 ^ k)
      have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * ((z ^ (2 ^ k) - 1) + 2) := by
        rw [pow_succ, pow_mul]; ring
      rw [e, norm_mul]
      have h3 : ‖(2 : ℂ)‖ ≤ ‖(z ^ (2 ^ k) - 1) + 2‖ + ‖z ^ (2 ^ k) - 1‖ := by
        have := norm_sub_le ((z ^ (2 ^ k) - 1) + 2) (z ^ (2 ^ k) - 1)
        simpa using this
      have h4 : ‖(2 : ℂ)‖ = 2 := by simp
      have h2 : (3 / 2 : ℝ) ≤ ‖(z ^ (2 ^ k) - 1) + 2‖ := by linarith
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖(z ^ (2 ^ k) - 1) + 2‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h6 : 1 < (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) := (div_lt_iff₀ (by positivity)).mp hk
  have h7 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
  have h8 := key k
  have h9 := h (2 ^ k)
  linarith

end Bl.SecondBlockLemmaN
