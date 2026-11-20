import Mathlib

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries

/- English proof (translation)
Introduce `j`. Take `⟨R, hR⟩` from `heq j`. Establish `h1 : coeff k (C p ^ K * (∑ m, F m * C (μ m j) - (if j = k₀ then C p ^ s * X ^ S * Q else 0))) = 0`. Rewrite using `[hR, coeff_X_pow_mul', if_neg (by omega)]`. Simplify using `only [← map_pow, coeff_C_mul, map_sub, map_sum, coeff_mul_C] at h1`.

Establish `h2` using `sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp))`. Rewrite using `[h2]`. Use `split_ifs with hj`. Simplify using `[← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hkS]`. Conclude with `map_zero _`.
-/
theorem coeff_relation {O : Type*} [CommRing O] [IsDomain O] {d₁ d : ℕ} (p : O) (hp : p ≠ 0)
    (F : Fin d₁ → O⟦X⟧) (μ : Fin d₁ → Fin d → O) (k₀ : Fin d) (K s S h k : ℕ) (Q : O⟦X⟧)
    (hk : k < h) (hkS : S ≤ k)
    (heq : ∀ j : Fin d, ∃ R : O⟦X⟧,
      C p ^ K * (∑ m, F m * C (μ m j) - (if j = k₀ then C p ^ s * X ^ S * Q else 0)) = X ^ h * R) :
    ∀ j, ∑ m, coeff k (F m) * μ m j = if j = k₀ then p ^ s * coeff (k - S) Q else 0 := by
  intro j
  obtain ⟨R, hR⟩ := heq j
  have h1 : coeff k (C p ^ K * (∑ m, F m * C (μ m j) -
      (if j = k₀ then C p ^ s * X ^ S * Q else 0))) = 0 := by
    rw [hR, coeff_X_pow_mul', if_neg (by omega)]
  simp only [← map_pow, coeff_C_mul, map_sub, map_sum, coeff_mul_C] at h1
  have h2 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp))
  rw [h2]
  split_ifs with hj
  · simp [← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hkS]
  · exact map_zero _

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
