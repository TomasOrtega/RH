import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
/- English proof (translation)
Use `⟨WithZero.log (w y), ?_⟩` and prove the remaining obligations. Rewrite using `[h, map_pow, two_mul, WithZero.exp_add, WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hy), sq]`.
-/
private lemma exists_exp_two_mul_of_eq_sq {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {u y : K}
    (hy : y ≠ 0) (h : w u = w (y ^ 2)) : ∃ n : ℤ, w u = WithZero.exp (2 * n) := by
  refine ⟨WithZero.log (w y), ?_⟩
  rw [h, map_pow, two_mul, WithZero.exp_add, WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hy),
    sq]

open NumberField IsDedekindDomain in
open scoped WithZero in

/- English proof (translation)
Introduce `K _ w ρ h2 hρ hroot a b hab`. Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Establish `ha : a ≠ 0` using `hab.resolve_right (not_not.mpr rfl)`. Conclude with `exists_exp_two_mul_of_eq_sq w ha (by congr 1; ring)`.

Use `set t := (a - b) / (2 * b) with ht_def`. Establish `hfac : a ^ 2 - (1 + 4 * ρ) * b ^ 2 = (2 * b) ^ 2 * (t ^ 2 + t - ρ)`. Rewrite using `[ht_def]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Distinguish the cases in `ht : w t ≤ 1`. Conclude with `exists_exp_two_mul_of_eq_sq w (mul_ne_zero h2 hb) (by rw [hfac, map_mul, hroot t ht, mul_one])`. Use `push_neg at ht`. Establish `ht0 : t ≠ 0`. Introduce and unpack `h`.

Rewrite `ht` using `[h, map_zero]`. Conclude with `not_lt_of_ge zero_le' ht`. Establish `hlt : w (t - ρ) < w (t ^ 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hval : w (t ^ 2 + t - ρ) = w (t ^ 2)`.

Rewrite using `[add_sub_assoc]`. Conclude with `Valuation.map_add_eq_of_lt_left w hlt`. Use `exists_exp_two_mul_of_eq_sq w (y := 2 * b * t) (mul_ne_zero (mul_ne_zero h2 hb) ht0) ?_` and prove the remaining obligations. Rewrite using `[hfac, map_mul, hval, ← map_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 →
      (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) →
        _root_.GlobalTheory.QNorm.EvenNorms w (1 + 4 * ρ) := by
  intro K _ w ρ h2 hρ hroot a b hab
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    exact exists_exp_two_mul_of_eq_sq w ha (by congr 1; ring)
  · set t := (a - b) / (2 * b) with ht_def
    have hfac : a ^ 2 - (1 + 4 * ρ) * b ^ 2 = (2 * b) ^ 2 * (t ^ 2 + t - ρ) := by
      rw [ht_def]
      field_simp
      ring
    by_cases ht : w t ≤ 1
    · exact exists_exp_two_mul_of_eq_sq w (mul_ne_zero h2 hb)
        (by rw [hfac, map_mul, hroot t ht, mul_one])
    · push_neg at ht
      have ht0 : t ≠ 0 := by
        rintro h
        rw [h, map_zero] at ht
        exact not_lt_of_ge zero_le' ht
      have hlt : w (t - ρ) < w (t ^ 2) := by
        calc w (t - ρ) ≤ max (w t) (w ρ) := Valuation.map_sub w t ρ
          _ = w t := max_eq_left (hρ.trans ht.le)
          _ < w t * w t := lt_mul_self ht
          _ = w (t ^ 2) := by rw [map_pow, sq]
      have hval : w (t ^ 2 + t - ρ) = w (t ^ 2) := by
        rw [add_sub_assoc]
        exact Valuation.map_add_eq_of_lt_left w hlt
      refine exists_exp_two_mul_of_eq_sq w (y := 2 * b * t) (mul_ne_zero (mul_ne_zero h2 hb) ht0) ?_
      rw [hfac, map_mul, hval, ← map_mul]
      congr 1
      ring

end GlobalTheory.QNorm
