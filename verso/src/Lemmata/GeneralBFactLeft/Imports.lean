import Mathlib

namespace Bl.general_b_fact_left

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
