import Mathlib

namespace UpperTheory.Reformulated.B.P6.r22b

/- English proof (translation)
Establish `e : 1 / a * (a * s) = s`. Rewrite using `[← mul_assoc, one_div_mul_cancel ha.ne', one_mul]`. Establish `has : 0 ≤ a * s` using `mul_nonneg ha.le hs`. Establish `hia : 0 < 1 / a` using `one_div_pos.mpr ha`. Establish `h1 : 1 + s ≤ (1 + 1 / a) * (1 + a * s)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 1 + a * s ≤ Real.exp (a * s)`. Combine the linear relations using `[Real.add_one_le_exp (a * s)]`. Establish `h3 : (1 + s) ^ K ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K`. Rewrite using `[← mul_pow]`.

Establish `h4 : 1 + s ≤ (1 + 1 / a) * Real.exp (a * s)` using `le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))`. Conclude with `pow_le_pow_left₀ (by linarith) h4 K`. Establish `h5 : Real.exp (a * s) ^ K * Real.exp (-β * s) ≤ 1`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add]`. Rewrite using `[Real.exp_le_one_iff]`.

Establish `: (K : ℝ) * (a * s) = ((K : ℝ) * a) * s` using `by ring`. Rewrite using `[this]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hKa hs]`. Establish `hc : 0 ≤ (1 + 1 / a) ^ K` using `pow_nonneg (by linarith) K`. Establish `hE : 0 ≤ Real.exp (-β * s)` using `(Real.exp_pos _).le`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_add_pow_mul_exp_neg_le_of_mul_le (K : ℕ) {a β s : ℝ} (ha : 0 < a) (hKa : (K : ℝ) * a ≤ β) (hs : 0 ≤ s) :
    (1 + s) ^ K * Real.exp (-β * s) ≤ (1 + 1 / a) ^ K := by
  have e : 1 / a * (a * s) = s := by
    rw [← mul_assoc, one_div_mul_cancel ha.ne', one_mul]
  have has : 0 ≤ a * s := mul_nonneg ha.le hs
  have hia : 0 < 1 / a := one_div_pos.mpr ha
  have h1 : 1 + s ≤ (1 + 1 / a) * (1 + a * s) := by
    calc 1 + s ≤ 1 + a * s + 1 / a + 1 / a * (a * s) := by rw [e]; linarith
      _ = (1 + 1 / a) * (1 + a * s) := by ring
  have h2 : 1 + a * s ≤ Real.exp (a * s) := by
    linarith [Real.add_one_le_exp (a * s)]
  have h3 : (1 + s) ^ K ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K := by
    rw [← mul_pow]
    have h4 : 1 + s ≤ (1 + 1 / a) * Real.exp (a * s) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
    exact pow_le_pow_left₀ (by linarith) h4 K
  have h5 : Real.exp (a * s) ^ K * Real.exp (-β * s) ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    have : (K : ℝ) * (a * s) = ((K : ℝ) * a) * s := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hKa hs]
  have hc : 0 ≤ (1 + 1 / a) ^ K := pow_nonneg (by linarith) K
  have hE : 0 ≤ Real.exp (-β * s) := (Real.exp_pos _).le
  calc (1 + s) ^ K * Real.exp (-β * s)
      ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K * Real.exp (-β * s) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = (1 + 1 / a) ^ K * (Real.exp (a * s) ^ K * Real.exp (-β * s)) := by ring
    _ ≤ (1 + 1 / a) ^ K * 1 := mul_le_mul_of_nonneg_left h5 hc
    _ = (1 + 1 / a) ^ K := mul_one _

/- English proof (translation)
Introduce `K β hβ`. Establish `hK : (0 : ℝ) < (K : ℝ) + 1` using `by positivity`. Establish `ha : 0 < β / ((K : ℝ) + 1)` using `div_pos hβ hK`. Establish `hKa : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ β`. Establish `e : ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) = β` using `by field_simp`.

Establish `: (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (β / ((K : ℝ) + 1))` using `mul_le_mul_of_nonneg_right (by linarith) ha.le`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨_, fun s hs => one_add_pow_mul_exp_neg_le_of_mul_le K ha hKa hs⟩`.
-/
theorem PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le :
    ∀ (K : ℕ) {β : ℝ}, OfNat.ofNat (nat_lit 0) < β → ∃ (M : ℝ), ∀ (s : ℝ), OfNat.ofNat (nat_lit 0) ≤ s → (OfNat.ofNat (nat_lit 1) + s) ^ K * Real.exp (-β * s) ≤ M := by
  intro K β hβ
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha : 0 < β / ((K : ℝ) + 1) := div_pos hβ hK
  have hKa : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ β := by
    have e : ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) = β := by field_simp
    have : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    linarith
  exact ⟨_, fun s hs => one_add_pow_mul_exp_neg_le_of_mul_le K ha hKa hs⟩

end UpperTheory.Reformulated.B.P6.r22b
