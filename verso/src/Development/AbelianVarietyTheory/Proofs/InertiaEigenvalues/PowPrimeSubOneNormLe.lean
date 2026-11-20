import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixOneAddPowSubEntryLeStatement

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ n _ _ X k hX i j`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (l : ℝ) ≠ 0` using `by positivity`. Use `set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht`. Establish `t0 : 0 ≤ t` using `by positivity`.

Establish `tl : t ≤ (l : ℝ)⁻¹`. Rewrite using `[ht, ← zpow_neg_one]`. Conclude with `zpow_le_zpow_right₀ hl1.le (by omega)`. Establish `t1 : t ≤ 1` using `tl.trans (inv_le_one_of_one_le₀ hl1.le)`. Establish `hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹`.

Rewrite using `[ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring, zpow_add₀ hl0, zpow_neg_one]`. Rewrite using `[hrhs]`. Use `set Y := X - 1 with hY`. Establish `hXY : X = 1 + Y` using `by rw [hY]; abel`. Establish `hR` using `GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hX l i j`.

Establish `hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j`. Rewrite using `[hXY]`. Simplify using the standard rewrite rules. Rewrite using `[hsplit]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (hX i j) (by positivity)`.
-/
theorem pow_prime_sub_one_norm_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  intro l _ n _ _ X k hX i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with ht
  have t0 : 0 ≤ t := by positivity
  have tl : t ≤ (l : ℝ)⁻¹ := by
    rw [ht, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have t1 : t ≤ 1 := tl.trans (inv_le_one_of_one_le₀ hl1.le)
  have hrhs : (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = t * (l : ℝ)⁻¹ := by
    rw [ht, show -(((k + 1 : ℕ) : ℤ) + 2) = -((k : ℤ) + 2) + (-1) by push_cast; ring,
      zpow_add₀ hl0, zpow_neg_one]
  rw [hrhs]
  set Y := X - 1 with hY
  have hXY : X = 1 + Y := by rw [hY]; abel
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hX l i j
  have hsplit : (X ^ l - 1) i j = ((1 + Y) ^ l - 1 - ((l : ℕ) : ℚ_[l]) • Y) i j + (((l : ℕ) : ℚ_[l]) • Y) i j := by
    rw [hXY]; simp
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · calc _ ≤ t ^ 2 := hR
      _ = t * t := sq t
      _ ≤ t * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_left tl t0
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p, mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i j) (by positivity)

end GlobalTheory
