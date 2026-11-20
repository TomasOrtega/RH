import Mathlib

namespace GlobalTheory.IntegralAlgebraMapNormBound

open Polynomial

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (c : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have h1 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] c)‖
      = ‖algebraMap ℤ_[l] ℚ_[l] c‖ := PadicAlgCl.norm_extends l _
  rw [h1]
  exact PadicInt.norm_le_one c

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hp⟩ := hx
  set n := p.natDegree with hn
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hlt
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, ← hn] at hp
  have hlead : p.coeff n = 1 := hmon
  rw [hlead, map_one, one_mul] at hp
  have heq : x ^ n = -∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hp
  have hbound : ‖∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ n / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖
        ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact norm_algebraMap_le_one _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ n := pow_le_pow_right₀ hlt.le (by omega)
  have hxn : ‖x‖ ^ n ≤ ‖x‖ ^ n / ‖x‖ := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = _ := by rw [heq, norm_neg]
      _ ≤ _ := hbound
  have hpos : 0 < ‖x‖ ^ n := pow_pos hx0 n
  have : ‖x‖ ^ n / ‖x‖ < ‖x‖ ^ n := div_lt_self hpos hlt
  linarith

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l),
    IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => norm_le_one_of_isIntegral x hx

end GlobalTheory.IntegralAlgebraMapNormBound
