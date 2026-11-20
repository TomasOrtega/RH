import Mathlib
open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hne : ∀ t : ℂ, t ≠ 0 → χ t ≠ 0`. Introduce `t ht h`. Use `hmul t t⁻¹ ht (inv_ne_zero ht)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ ht, h1, h, zero_mul]`. Conclude with `one_ne_zero this`.

Establish `hp0 : p ≠ 0`. Introduce `h`. Use `hp 1 one_ne_zero` as an intermediate fact. Rewrite `this` using `[h, eval_zero, one_pow, one_mul, h1]`. Conclude with `one_ne_zero this`.

Take `⟨q, hpq, hdvd⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0`. Establish `hq : ∀ t : ℂ, q.eval t ≠ 0`. Introduce `t ht`. Distinguish the cases in `t0 : t = 0`. Substitute `t0` using the available equality.

Apply `hdvd` to reduce the goal to its premises. Rewrite using `[dvd_iff_isRoot]`. Conclude with `ht`. Use `hp t t0` as an intermediate fact. Rewrite `this` using `[hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, ht, mul_zero]`.

Conclude with `mul_ne_zero (pow_ne_zero _ t0) (hne t t0) this`. Establish `hdeg : q.natDegree = 0`. Assume the negation of the conclusion as `hd`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hq 0 (eval_zero)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root q (by`. Rewrite using `[degree_eq_natDegree hq0]`. Conclude with `hd)` after adjusting the coercions. Conclude with `hq z hz`.

Rewrite `hpq` using `[eq_C_of_natDegree_eq_zero hdeg]`. Establish `hc : q.coeff 0 = 1`. Use `hp 1 one_ne_zero` as an intermediate fact. Rewrite `this` using `[hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, one_pow, one_pow, one_mul, one_mul, h1]`. Conclude with `this.symm`.

Use `⟨(rootMultiplicity 0 p : ℤ) - N, fun t ht => ?_⟩` and prove the remaining obligations. Use `hp t ht` as an intermediate fact. Rewrite `this` using `[hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, hc, mul_one]`. Rewrite using `[zpow_sub₀ ht, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ ht), mul_comm, this]`.
-/
theorem mono_char_of_mul_poly_div_pow (χ : ℂ → ℂ)
    (hmul : ∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) (h1 : χ 1 = 1) (N : ℕ)
    (p : Polynomial ℂ) (hp : ∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) :
    ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  have hne : ∀ t : ℂ, t ≠ 0 → χ t ≠ 0 := by
    intro t ht h
    have := hmul t t⁻¹ ht (inv_ne_zero ht)
    rw [mul_inv_cancel₀ ht, h1, h, zero_mul] at this
    exact one_ne_zero this
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 1 one_ne_zero
    rw [h, eval_zero, one_pow, one_mul, h1] at this
    exact one_ne_zero this
  obtain ⟨q, hpq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hq : ∀ t : ℂ, q.eval t ≠ 0 := by
    intro t ht
    by_cases t0 : t = 0
    · subst t0
      apply hdvd
      rw [dvd_iff_isRoot]
      exact ht
    · have := hp t t0
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, ht, mul_zero] at this
      exact mul_ne_zero (pow_ne_zero _ t0) (hne t t0) this
  have hdeg : q.natDegree = 0 := by
    by_contra hd
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hq 0 (eval_zero)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q (by
      rw [degree_eq_natDegree hq0]
      exact_mod_cast hd)
    exact hq z hz
  rw [eq_C_of_natDegree_eq_zero hdeg] at hpq
  have hc : q.coeff 0 = 1 := by
    have := hp 1 one_ne_zero
    rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, one_pow, one_pow,
      one_mul, one_mul, h1] at this
    exact this.symm
  refine ⟨(rootMultiplicity 0 p : ℤ) - N, fun t ht => ?_⟩
  have := hp t ht
  rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, hc, mul_one] at this
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ ht), mul_comm, this]

end GlobalTheory
