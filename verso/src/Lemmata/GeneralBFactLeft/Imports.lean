import Mathlib

namespace Bl.general_b_fact_left

/- English proof (translation)
Introduce `k _ _ t m e hd`. Distinguish the cases in `hc : ringChar k = 2`. Establish `h2 : (2 : k) = 0`. Use `ringChar.Nat.cast_ringChar (R := k)` as an intermediate fact. Rewrite `this` using `[hc, Nat.cast_ofNat]`. Then use the resulting hypothesis.

Establish `h4 : (4 : k) = 0`. Establish `: (4 : k) = 2 * 2` using `by norm_num`. Rewrite using `[this, h2, zero_mul]`. Rewrite `hd` using `[h4, zero_mul, sub_zero]`. Establish `ht : t ≠ 0` using `fun h => hd (by rw [h]; ring)`.

Distinguish the cases in `hm : m = 0`. Use `⟨1, (e - 1) / t, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr⟩` from `FiniteField.isSquare_of_char_two hc (e / m)`. Use `⟨0, r, ?_⟩` and prove the remaining obligations. Establish `: r ^ 2 = e / m` using `by rw [hr]; ring`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (2 : k) ≠ 0` using `Ring.two_ne_zero hc`. Establish `h4 : (4 : k) ≠ 0`. Establish `: (4 : k) = 2 * 2` using `by norm_num`. Rewrite using `[this]`.

Conclude with `mul_ne_zero h2 h2`. Use `set D : k := m - t ^ 2 / 4 with hD`. Establish `hD0 : D ≠ 0`. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Establish `: t ^ 2 - 4 * m = -4 * D` using `by rw [hD]; field_simp; ring`. Rewrite using `[this, h0, mul_zero]`. Establish `hf : Polynomial.degree (Polynomial.X ^ 2 - Polynomial.C e : Polynomial k) = 2`. Apply the tactic sequence `rw [Polynomial.degree_sub_C] <;> rw [Polynomial.degree_X_pow] <;> norm_num`. Establish `hg : Polynomial.degree (Polynomial.C D * Polynomial.X ^ 2 : Polynomial k) = 2`.

Rewrite using `[Polynomial.degree_C_mul_X_pow 2 hD0]`. Both sides reduce to the same expression. Take `⟨a, b, hab⟩` from `FiniteField.exists_root_sum_quadratic hf hg (FiniteField.odd_card_of_char_ne_two hc)`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul] at hab`. Use `⟨a - t * b / 2, b, ?_⟩` and prove the remaining obligations.

Establish `key : a ^ 2 + D * b ^ 2 = e` using `by linear_combination hab`. Rewrite using `[← key, hD]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by
  intro k _ _ t m e hd
  by_cases hc : ringChar k = 2
  · have h2 : (2 : k) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := k)
      rwa [hc, Nat.cast_ofNat] at this
    have h4 : (4 : k) = 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this, h2, zero_mul]
    rw [h4, zero_mul, sub_zero] at hd
    have ht : t ≠ 0 := fun h => hd (by rw [h]; ring)
    by_cases hm : m = 0
    · refine ⟨1, (e - 1) / t, ?_⟩
      rw [hm]
      field_simp
      ring
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hc (e / m)
      refine ⟨0, r, ?_⟩
      have : r ^ 2 = e / m := by rw [hr]; ring
      rw [this]
      field_simp
      ring
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hc
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    set D : k := m - t ^ 2 / 4 with hD
    have hD0 : D ≠ 0 := by
      intro h0
      apply hd
      have : t ^ 2 - 4 * m = -4 * D := by rw [hD]; field_simp; ring
      rw [this, h0, mul_zero]
    have hf : Polynomial.degree (Polynomial.X ^ 2 - Polynomial.C e : Polynomial k) = 2 := by
      rw [Polynomial.degree_sub_C] <;> rw [Polynomial.degree_X_pow] <;> norm_num
    have hg : Polynomial.degree (Polynomial.C D * Polynomial.X ^ 2 : Polynomial k) = 2 := by
      rw [Polynomial.degree_C_mul_X_pow 2 hD0]; rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg
      (FiniteField.odd_card_of_char_ne_two hc)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul] at hab
    refine ⟨a - t * b / 2, b, ?_⟩
    have key : a ^ 2 + D * b ^ 2 = e := by linear_combination hab
    rw [← key, hD]
    field_simp
    ring

end Bl.general_b_fact_left
