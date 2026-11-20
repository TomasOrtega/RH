import Mathlib

universe u_1

namespace Bl.general_b_fact_third

/- English proof (translation)
Introduce `K _ _ P hP hc x hx`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Establish `hx0 : (0:ℝ) < ‖x‖` using `lt_trans one_pos h`. Rewrite `hx` using `[Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul]`.

Establish `hS : ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i‖ ≤ ‖x‖ ^ P.natDegree / ‖x‖`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[norm_mul, norm_pow, le_div_iff₀ hx0]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hc i`. Use `_ = ‖x‖ ^ (i + 1) := by rw [one_mul, pow_succ]`. Use `_ ≤ ‖x‖ ^ P.natDegree := pow_le_pow_right₀ h.le (Nat.succ_le_of_lt hi)`. Establish `heq : ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i = -(x ^ P.natDegree)` using `eq_neg_of_add_eq_zero_left hx`.

Rewrite `hS` using `[heq, norm_neg, norm_pow]`. Establish `hpos : 0 < ‖x‖ ^ P.natDegree` using `pow_pos hx0 _`. Establish `hlt : ‖x‖ ^ P.natDegree / ‖x‖ < ‖x‖ ^ P.natDegree` using `div_lt_self hpos h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem goal1 :
  ∀ {K : Type u_1} [inst : NormedField.{u_1} K] [IsUltrametricDist.{u_1} K] (P : Polynomial.{u_1} K),
  Polynomial.Monic.{u_1} P →
    (∀ (i : Nat), LE.le.{0} (Norm.norm.{u_1} (Polynomial.coeff.{u_1} P i)) 1) →
      ∀ (x : K), Eq.{u_1 + 1} (Polynomial.eval.{u_1} x P) 0 → LE.le.{0} (Norm.norm.{u_1} x) 1 := by
  intro K _ _ P hP hc x hx
  by_contra h
  rw [not_le] at h
  have hx0 : (0:ℝ) < ‖x‖ := lt_trans one_pos h
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_mul] at hx
  have hS : ‖∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i‖ ≤ ‖x‖ ^ P.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖P.coeff i‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact hc i
      _ = ‖x‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖x‖ ^ P.natDegree := pow_le_pow_right₀ h.le (Nat.succ_le_of_lt hi)
  have heq : ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i = -(x ^ P.natDegree) :=
    eq_neg_of_add_eq_zero_left hx
  rw [heq, norm_neg, norm_pow] at hS
  have hpos : 0 < ‖x‖ ^ P.natDegree := pow_pos hx0 _
  have hlt : ‖x‖ ^ P.natDegree / ‖x‖ < ‖x‖ ^ P.natDegree := div_lt_self hpos h
  linarith

end Bl.general_b_fact_third
