import Mathlib

namespace GlobalTheory.IntegralNormLeOne

open Polynomial

/- English proof (translation)
Establish `hc : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1`. Introduce `a`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`. Conclude with `a.2`. Take `⟨p, hm, hp⟩` from `hx`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : (0 : ℝ) < ‖x‖` using `lt_trans one_pos h`. Rewrite `hp` using `[hm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum]`. Establish `he : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i)` using `eq_neg_of_add_eq_zero_left hp`.

Break down `Nat.eq_zero_or_pos p.natDegree with hn | hn` into its components or cases. Rewrite `he` using `[hn]`. Simplify using `at he`. Establish `hle : ‖∑ i ∈ Finset.range p.natDegree, eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i)‖ ≤ ‖x‖ ^ (p.natDegree - 1)`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises.

Introduce `i hi`. Establish `hi' : i ≤ p.natDegree - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, norm_mul, norm_pow]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1)`. Rewrite using `[← norm_pow, he, norm_neg]`. Conclude with `hle`. Establish `h2 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree` using `pow_lt_pow_right₀ h (by omega)`.

Conclude with `absurd h1 (not_le.mpr h2)`.
-/
theorem norm_le_one_of_isIntegral {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  have hc : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have h0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos h
  rw [hm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum] at hp
  have he : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i) :=
    eq_neg_of_add_eq_zero_left hp
  rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
  · rw [hn] at he
    simp at he
  · have hle : ‖∑ i ∈ Finset.range p.natDegree,
        eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i)‖
        ≤ ‖x‖ ^ (p.natDegree - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      have hi' : i ≤ p.natDegree - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, norm_mul, norm_pow]
      calc _ ≤ 1 * ‖x‖ ^ i := by gcongr; exact hc _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ _ := pow_le_pow_right₀ h.le hi'
    have h1 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
      rw [← norm_pow, he, norm_neg]; exact hle
    have h2 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree :=
      pow_lt_pow_right₀ h (by omega)
    exact absurd h1 (not_le.mpr h2)

end GlobalTheory.IntegralNormLeOne
