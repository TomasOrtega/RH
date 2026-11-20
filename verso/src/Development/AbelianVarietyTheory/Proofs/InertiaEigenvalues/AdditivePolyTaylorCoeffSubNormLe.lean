import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `l hl E a W ha hW j hj`. Establish `hp : l.Prime` using `hl.out`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_` and prove the remaining obligations. Establish `hak : ‖a k‖ ≤ 1` using `ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))`.

Rewrite using `[Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]`. Break down `lt_trichotomy j (l ^ k) with h | h | h` into its components or cases. Establish `hne : j ≠ l ^ k` using `h.ne`. Simplify using `only [hne, if_false, mul_zero, sub_zero]`. Take `⟨m, hm⟩ : l ∣ (l ^ k).choose j` from `hp.dvd_choose_pow (by omega) h.ne`.

Rewrite using `[hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]`. Establish `h1 : ‖W ^ (l ^ k - j)‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW`. Establish `h2 : ‖(m : ℂ_[l])‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one _ m`. Combine the equalities or inequalities in the displayed calculation. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `hne : j ≠ l ^ k` using `h.ne'`. Simplify using `only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]`. Simplify using the standard rewrite rules.
-/
theorem additive_poly_taylor_coeff_sub_norm_le :
    ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro l hl E a W ha hW j hj
  have hp : l.Prime := hl.out
  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
  have hak : ‖a k‖ ≤ 1 := ha k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [Polynomial.taylor_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_pow]
  rcases lt_trichotomy j (l ^ k) with h | h | h
  · have hne : j ≠ l ^ k := h.ne
    simp only [hne, if_false, mul_zero, sub_zero]
    obtain ⟨m, hm⟩ : l ∣ (l ^ k).choose j := hp.dvd_choose_pow (by omega) h.ne
    rw [hm, Nat.cast_mul, norm_mul, norm_mul, norm_mul]
    have h1 : ‖W ^ (l ^ k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hW
    have h2 : ‖(m : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
    calc ‖a k‖ * (‖W ^ (l ^ k - j)‖ * (‖(l : ℂ_[l])‖ * ‖(m : ℂ_[l])‖))
        ≤ 1 * (1 * (‖(l : ℂ_[l])‖ * 1)) := by gcongr
      _ = ‖(l : ℂ_[l])‖ := by ring
  · subst h
    simp
  · have hne : j ≠ l ^ k := h.ne'
    simp only [hne, if_false, mul_zero, sub_zero, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
    simp

end GlobalTheory
