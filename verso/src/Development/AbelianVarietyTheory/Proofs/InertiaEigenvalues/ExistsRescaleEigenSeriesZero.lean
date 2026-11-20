import Mathlib

open PowerSeries

namespace GlobalTheory

noncomputable def eigenSeriesCoeff {F : Type} [Field F] (a c : ℕ → F) : ℕ → F
  | 0 => 1
  | k + 1 => (a (k + 1))⁻¹ * ∑ i : Fin (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i)
decreasing_by omega

/- English proof (translation)
Rewrite using `[eigenSeriesCoeff, mul_inv_cancel_left₀ ha]`. Conclude with `Fin.sum_univ_eq_sum_range (fun i => c (i + 1) * eigenSeriesCoeff a c (k - i)) (k + 1)`.
-/
theorem eigenSeriesCoeff_succ {F : Type} [Field F] (a c : ℕ → F) (k : ℕ) (ha : a (k + 1) ≠ 0) :
    a (k + 1) * eigenSeriesCoeff a c (k + 1)
      = ∑ i ∈ Finset.range (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i) := by
  rw [eigenSeriesCoeff, mul_inv_cancel_left₀ ha]
  exact Fin.sum_univ_eq_sum_range (fun i => c (i + 1) * eigenSeriesCoeff a c (k - i)) (k + 1)

/- English proof (translation)
Use `set L : F := (u - 1) / constantCoeff p with hL`. Establish `hLp : L * coeff 0 p = u - 1`. Rewrite using `[coeff_zero_eq_constantCoeff_apply, hL]`. Clear the denominators using the available nonvanishing facts. Use `⟨PowerSeries.mk (eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_mk, eigenSeriesCoeff]`. Use extensionality with `k`. Simplify using `only [map_sub, coeff_C_mul, coeff_rescale, coeff_mk]`. Rewrite using `[coeff_mul]`. Simplify using `only [coeff_mk]`.

Consider the cases of `k with`. Consider the case `zero`. Simplify using `only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero]`. Rewrite using `[eigenSeriesCoeff]`. Take the linear combination `-hLp`.

Consider the case `succ k`. Establish `ha : u * (χ ^ (k + 1) - 1) ≠ 0` using `mul_ne_zero hu (sub_ne_zero.mpr (hχ (k + 1) (Nat.succ_pos k)))`. Establish `key` using `eigenSeriesCoeff_succ (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) k ha`. Simplify using `only [mul_assoc] at key`. Rewrite `key` using `[← Finset.mul_sum]`.

Rewrite using `[Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [Nat.succ_eq_add_one]`. Take the linear combination `key - eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) (k + 1) * hLp`.
-/
theorem exists_rescale_eigen_series_zero {F : Type} [Field F] (p : F⟦X⟧) (χ u : F)
    (hp : constantCoeff p ≠ 0) (hu : u ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1) :
    ∃ h : F⟦X⟧, constantCoeff h = 1 ∧
      C u * rescale χ h - h = C ((u - 1) / constantCoeff p) * (p * h) := by
  set L : F := (u - 1) / constantCoeff p with hL
  have hLp : L * coeff 0 p = u - 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, hL]
    field_simp
  refine ⟨PowerSeries.mk (eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p)),
    ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, eigenSeriesCoeff]
  · ext k
    simp only [map_sub, coeff_C_mul, coeff_rescale, coeff_mk]
    rw [coeff_mul]
    simp only [coeff_mk]
    cases k with
    | zero =>
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero]
      rw [eigenSeriesCoeff]
      linear_combination -hLp
    | succ k =>
      have ha : u * (χ ^ (k + 1) - 1) ≠ 0 :=
        mul_ne_zero hu (sub_ne_zero.mpr (hχ (k + 1) (Nat.succ_pos k)))
      have key := eigenSeriesCoeff_succ (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) k ha
      simp only [mul_assoc] at key
      rw [← Finset.mul_sum] at key
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Nat.succ_eq_add_one]
      linear_combination key - eigenSeriesCoeff (fun k => u * (χ ^ k - 1))
        (fun j => L * coeff j p) (k + 1) * hLp

/- English proof (translation)
Introduce `F _ p χ κ n hp hκ hχ0 hχ`. Take `⟨h, h0, hh⟩` from `exists_rescale_eigen_series_zero p χ (κ * χ ^ n) hp (mul_ne_zero hκ (pow_ne_zero n hχ0)) hχ`. Use `⟨h, h0, ?_⟩` and prove the remaining obligations. Establish `hX : rescale χ (X ^ n * h) = C (χ ^ n) * X ^ n * rescale χ h`. Rewrite using `[map_mul, map_pow, rescale_X, mul_pow, map_pow]`.

Rewrite using `[hX]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_rescale_eigen_series : ∀ {F : Type} [Field F] (p : F⟦X⟧) (χ κ : F) (n : ℕ), constantCoeff p ≠ 0 → κ ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → ∃ h : F⟦X⟧, constantCoeff h = 1 ∧ C κ * rescale χ (X ^ n * h) - X ^ n * h = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by
  intro F _ p χ κ n hp hκ hχ0 hχ
  obtain ⟨h, h0, hh⟩ :=
    exists_rescale_eigen_series_zero p χ (κ * χ ^ n) hp (mul_ne_zero hκ (pow_ne_zero n hχ0)) hχ
  refine ⟨h, h0, ?_⟩
  have hX : rescale χ (X ^ n * h) = C (χ ^ n) * X ^ n * rescale χ h := by
    rw [map_mul, map_pow, rescale_X, mul_pow, map_pow]
  rw [hX]
  calc C κ * (C (χ ^ n) * X ^ n * rescale χ h) - X ^ n * h
      = X ^ n * (C (κ * χ ^ n) * rescale χ h - h) := by rw [map_mul]; ring
    _ = X ^ n * (C ((κ * χ ^ n - 1) / constantCoeff p) * (p * h)) := by rw [hh]
    _ = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by ring

end GlobalTheory
