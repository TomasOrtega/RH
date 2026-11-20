import Mathlib

namespace GlobalTheory.IntegralCoefficientNormBound

open Polynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_norm_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rw [show algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)
      = ((algebraMap ℤ_[l] ℚ_[l] a : ℚ_[l]) : PadicAlgCl l) from rfl, PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem norm_le_one_of_isIntegral :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
  have key : (aeval x p) = x ^ p.natDegree +
      ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    conv_lhs => rw [hm.as_sum]
    simp [map_add, map_sum, aeval_C, aeval_X_pow]
  rw [← aeval_def] at hp
  rw [hp] at key
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at key
    simp at key
  have hsum : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ (p.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr
          exact coeff_norm_le_one l _
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (p.natDegree - 1) := pow_le_pow_right₀ hx1 (by omega)
  have heq : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := eq_neg_of_add_eq_zero_left key.symm
  have : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]; exact hsum
  have hlt : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

end GlobalTheory.IntegralCoefficientNormBound
