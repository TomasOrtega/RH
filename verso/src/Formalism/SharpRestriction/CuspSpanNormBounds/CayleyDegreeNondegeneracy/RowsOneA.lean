import Mathlib

namespace Formalism.MainNotions.BridgeLemma₂

/- English proof (translation)
Establish `hk0 : (0:ℝ) < k` using `Nat.cast_pos.mpr (by omega)`. Establish `hkne : (k:ℝ) ≠ 0` using `hk0.ne'`. Establish `hC0 : 0 < C` using `by linarith`. Establish `hr0 : (0:ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hb0 : 0 < C / k` using `div_pos hC0 hk0`.

Establish `hCk' : C ≤ k`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hC0.le (sub_nonneg.2 hC)) (by linarith : (0:ℝ) ≤ C + 1)]`. Establish `hb1 : C / k ≤ 1` using `by rw [div_le_iff₀ hk0]; linarith`. Establish `he : (3:ℝ) * ((r:ℝ) / 2) ≤ 2 * (r : ℝ) * (1 - δ)`. Use polynomial arithmetic with `[mul_nonneg hr0 (sub_nonneg.2 hδ)]`.

Establish `hb3 : (C / k) ^ 3 ≤ ((k:ℝ) ^ 2)⁻¹`. Rewrite using `[div_pow, div_le_iff₀ (pow_pos hk0 3)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[eq_comm, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hkne)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hkr : (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) = ((k:ℝ) ^ r)⁻¹`. Rewrite using `[Real.inv_rpow (pow_nonneg hk0.le 2)]`. Use `congr 1`. Rewrite using `[← Real.rpow_natCast (k:ℝ) 2, ← Real.rpow_mul hk0.le, ← Real.rpow_natCast (k:ℝ) r]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_mul hb0.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]`. Use `_ ≤ (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) := Real.rpow_le_rpow (pow_nonneg hb0.le 3) hb3 (by positivity)`.

Use `_ = ((k:ℝ) ^ r)⁻¹ := hkr`.
-/
theorem div_rpow_le_inv_pow {k r : ℕ} {C δ : ℝ} (hk : 1 ≤ k) (hC : 1 ≤ C) (hδ : δ ≤ 1 / 4) (hCk : C ^ 3 ≤ k) :
    (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ ((k : ℝ) ^ r)⁻¹ := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hkne : (k:ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hb0 : 0 < C / k := div_pos hC0 hk0
  have hCk' : C ≤ k := by
    nlinarith [mul_nonneg (mul_nonneg hC0.le (sub_nonneg.2 hC)) (by linarith : (0:ℝ) ≤ C + 1)]
  have hb1 : C / k ≤ 1 := by rw [div_le_iff₀ hk0]; linarith
  have he : (3:ℝ) * ((r:ℝ) / 2) ≤ 2 * (r : ℝ) * (1 - δ) := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.2 hδ)]
  have hb3 : (C / k) ^ 3 ≤ ((k:ℝ) ^ 2)⁻¹ := by
    rw [div_pow, div_le_iff₀ (pow_pos hk0 3)]
    calc C ^ 3 ≤ k := hCk
      _ = ((k:ℝ) ^ 2)⁻¹ * (k:ℝ) ^ 3 := by
        rw [eq_comm, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hkne)]; ring
  have hkr : (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) = ((k:ℝ) ^ r)⁻¹ := by
    rw [Real.inv_rpow (pow_nonneg hk0.le 2)]
    congr 1
    rw [← Real.rpow_natCast (k:ℝ) 2, ← Real.rpow_mul hk0.le, ← Real.rpow_natCast (k:ℝ) r]
    congr 1; push_cast; ring
  calc (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ (C / k) ^ ((3:ℝ) * ((r:ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hb0 hb1 he
    _ = ((C / k) ^ 3) ^ ((r:ℝ) / 2) := by
        rw [Real.rpow_mul hb0.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ ≤ (((k:ℝ) ^ 2)⁻¹) ^ ((r:ℝ) / 2) :=
        Real.rpow_le_rpow (pow_nonneg hb0.le 3) hb3 (by positivity)
    _ = ((k:ℝ) ^ r)⁻¹ := hkr

end Formalism.MainNotions.BridgeLemma₂
