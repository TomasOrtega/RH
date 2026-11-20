import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Helly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.LteNorm

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Use `set A := algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])`. Use `set B := algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l])`. Establish `hA : ‖A‖ = 1`. Simplify using `only [A, PadicAlgCl.norm_extends, ← PadicInt.norm_def, ha]`. Establish `hAB : ‖A - B‖ = ‖a - b‖`.

Simplify using `only [A, B, ← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, ← PadicInt.norm_def]`. Establish `hdiff : A * z - 1 - (B * z - 1) = (A - B) * z` using `by ring`. Establish `hmax : ‖A * z - 1 - (B * z - 1)‖ ≤ max ‖A * z - 1‖ ‖B * z - 1‖`. Use `IsUltrametricDist.norm_add_le_max (A * z - 1) (-(B * z - 1))` as an intermediate fact. Rewrite `this` using `[norm_neg, ← sub_eq_add_neg]`. Then use the resulting hypothesis.

Break down `le_or_gt 1 ‖z‖ with hz | hz` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Establish `hAz : ‖A * z‖ < 1` using `by rw [norm_mul, hA, one_mul]; exact hz`. Establish `h1 : (1 : ℝ) ≤ ‖A * z - 1‖`. Use `IsUltrametricDist.norm_add_le_max (A * z) (-(A * z - 1))` as an intermediate fact.

Rewrite `this` using `[norm_neg, show A * z + -(A * z - 1) = 1 by ring, norm_one]`. Break down `le_max_iff.mp this with h | h` into its components or cases. Conclude with `absurd h (not_le.mpr hAz)`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem padic_units_distance_le_max (l : ℕ) [Fact l.Prime] (a b : ℤ_[l]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (z : PadicAlgCl l) :
    ‖a - b‖ ≤ max ‖algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l]) * z - 1‖
      ‖algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l]) * z - 1‖ := by
  set A := algebraMap ℚ_[l] (PadicAlgCl l) (a : ℚ_[l])
  set B := algebraMap ℚ_[l] (PadicAlgCl l) (b : ℚ_[l])
  have hA : ‖A‖ = 1 := by
    simp only [A, PadicAlgCl.norm_extends, ← PadicInt.norm_def, ha]
  have hAB : ‖A - B‖ = ‖a - b‖ := by
    simp only [A, B, ← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, ← PadicInt.norm_def]
  have hdiff : A * z - 1 - (B * z - 1) = (A - B) * z := by ring
  have hmax : ‖A * z - 1 - (B * z - 1)‖ ≤ max ‖A * z - 1‖ ‖B * z - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max (A * z - 1) (-(B * z - 1))
    rwa [norm_neg, ← sub_eq_add_neg] at this
  rcases le_or_gt 1 ‖z‖ with hz | hz
  · calc ‖a - b‖ ≤ ‖a - b‖ * ‖z‖ := le_mul_of_one_le_right (norm_nonneg _) hz
      _ = ‖A * z - 1 - (B * z - 1)‖ := by rw [hdiff, norm_mul, hAB]
      _ ≤ _ := hmax
  · have hAz : ‖A * z‖ < 1 := by rw [norm_mul, hA, one_mul]; exact hz
    have h1 : (1 : ℝ) ≤ ‖A * z - 1‖ := by
      have := IsUltrametricDist.norm_add_le_max (A * z) (-(A * z - 1))
      rw [norm_neg, show A * z + -(A * z - 1) = 1 by ring, norm_one] at this
      rcases le_max_iff.mp this with h | h
      · exact absurd h (not_le.mpr hAz)
      · exact h
    calc ‖a - b‖ ≤ 1 := PadicInt.norm_le_one _
      _ ≤ ‖A * z - 1‖ := h1
      _ ≤ _ := le_max_left _ _

/- English proof (translation)
Introduce `l _ u c hc j z`. Take `⟨hu, -, hdist⟩` from `lteNorm l u c hc`. Establish `hK : (0 : ℝ) < (l : ℝ) ^ (j + c)`. Establish `: (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Check the signs of the components of the expression.

Use `set r : ℕ → ℝ := fun e => (l : ℝ) ^ (j + c) * ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ with hr`. Establish `hunit : ∀ e : ℕ, ‖((u ^ l ^ j) ^ e : ℤ_[l])‖ = 1`. Introduce `e`. Rewrite using `[← pow_mul, norm_pow, hu, one_pow]`. Take `⟨s, hs⟩` from `helly l (fun e : ℕ => (e : ℤ_[l])) r (by`.

Introduce `a b`. Establish `key` using `padic_units_distance_le_max l _ _ (hunit a) (hunit b) z`. Establish `h` using `hdist j a b`. Establish `: ‖(a : ℤ_[l]) - b‖ = (l : ℝ) ^ (j + c) * ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖`. Rewrite using `[h, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]`.

Simplify using `only [this, hr]`. Rewrite using `[← mul_max_of_nonneg _ _ hK.le]`. Conclude with `mul_le_mul_of_nonneg_left key hK.le)`. Use `⟨s, fun e => ?_⟩` and prove the remaining obligations. Use `hs e` as an intermediate fact.

Simplify using `only [hr] at this`. Rewrite using `[inv_mul_le_iff₀ hK]`. Conclude with `this`.
-/
theorem UpperTheory.V.PropA.ball :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j : ℕ) (z : PadicAlgCl l), ∃ s : ℤ_[l], ∀ e : ℕ,
      ((l : ℝ) ^ (j + c))⁻¹ * ‖s - e‖ ≤ ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ := by
  intro l _ u c hc j z
  obtain ⟨hu, -, hdist⟩ := lteNorm l u c hc
  have hK : (0 : ℝ) < (l : ℝ) ^ (j + c) := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  set r : ℕ → ℝ := fun e =>
    (l : ℝ) ^ (j + c) * ‖algebraMap ℚ_[l] (PadicAlgCl l) (((u ^ l ^ j) ^ e : ℤ_[l]) : ℚ_[l]) * z - 1‖ with hr
  have hunit : ∀ e : ℕ, ‖((u ^ l ^ j) ^ e : ℤ_[l])‖ = 1 := by
    intro e
    rw [← pow_mul, norm_pow, hu, one_pow]
  obtain ⟨s, hs⟩ := helly l (fun e : ℕ => (e : ℤ_[l])) r (by
    intro a b
    have key := padic_units_distance_le_max l _ _ (hunit a) (hunit b) z
    have h := hdist j a b
    have : ‖(a : ℤ_[l]) - b‖ = (l : ℝ) ^ (j + c) * ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
    simp only [this, hr]
    rw [← mul_max_of_nonneg _ _ hK.le]
    exact mul_le_mul_of_nonneg_left key hK.le)
  refine ⟨s, fun e => ?_⟩
  have := hs e
  simp only [hr] at this
  rw [inv_mul_le_iff₀ hK]
  exact this
