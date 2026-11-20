import Mathlib

namespace GlobalTheory.PadicIntegralNormLeOne

open Polynomial

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]`. Conclude with `PadicInt.norm_le_one a`.
-/
theorem norm_algebraMap_padicInt_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
    PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

/- English proof (translation)
Take `⟨f, hmon, hf⟩` from `hx`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hsum` using `hf`. Rewrite `hsum` using `[eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree, hmon.leadingCoeff, map_one, one_mul]`.

Use `set n := f.natDegree`. Use `set S := ∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i`. Establish `hxn : x ^ n = -S` using `by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Establish `: S = 0` using `by simp [S, hn]`.

Rewrite `hxn` using `[this, hn, pow_zero, neg_zero]`. Conclude with `one_ne_zero hxn`. Establish `hx1 : (1 : ℝ) ≤ ‖x‖` using `h.le`. Establish `hS : ‖S‖ ≤ ‖x‖ ^ (n - 1)`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n` using `pow_lt_pow_right₀ h (by omega)`.

Establish `: ‖x ^ n‖ = ‖S‖` using `by rw [hxn, norm_neg]`. Rewrite `this` using `[norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra h
  push_neg at h
  have hsum := hf
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree, hmon.leadingCoeff,
    map_one, one_mul] at hsum
  set n := f.natDegree
  set S := ∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i
  have hxn : x ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : S = 0 := by simp [S, hn]
    rw [this, hn, pow_zero, neg_zero] at hxn
    exact one_ne_zero hxn
  · have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
    have hS : ‖S‖ ≤ ‖x‖ ^ (n - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow]
      calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr; exact norm_algebraMap_padicInt_le_one _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ hx1 (by omega)
    have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
    have : ‖x ^ n‖ = ‖S‖ := by rw [hxn, norm_neg]
    rw [norm_pow] at this
    linarith

end GlobalTheory.PadicIntegralNormLeOne

/- English proof (translation)
Introduce `x hx` and use `GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral x hx`.
-/
example : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral x hx
