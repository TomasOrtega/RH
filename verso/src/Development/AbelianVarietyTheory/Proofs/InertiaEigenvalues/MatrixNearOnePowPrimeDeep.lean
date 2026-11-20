import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixOneAddPowSubEntryLeStatement

namespace GlobalTheory

/- English proof (translation)
Introduce `l hl n _ _ X k h1 h2 i j`. Establish `hL : (2:ℝ) ≤ l` using `by exact_mod_cast hl.out.two_le`. Establish `hLpos : (0:ℝ) < l` using `by linarith`. Use `set u : ℝ := (l:ℝ)⁻¹ with hu`. Establish `u0 : 0 < u` using `inv_pos.mpr hLpos`.

Establish `uhalf : u ≤ 1 / 2`. Rewrite using `[hu, one_div]; exact inv_anti₀ (by norm_num) hL`. Establish `hz : ∀ m : ℕ, (l:ℝ) ^ (-(m:ℤ)) = u ^ m` using `fun m => by`. Rewrite using `[zpow_neg, zpow_natCast, inv_pow]`. Establish `e2 : (l:ℝ) ^ (-2:ℤ) = u ^ 2` using `hz 2`.

Establish `e3 : (l:ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = u ^ (k + 3)`. Rewrite using `[← hz]`. Use `congr 1`. Establish `e4 : (l:ℝ) ^ (-((k : ℤ) + 2)) = u ^ (k + 2)`. Rewrite using `[← hz]`.

Use `congr 1`. Rewrite using `[e4]`. Use `set Y := X - 1 with hY`. Use `haveI : Nonempty (n × n) := ⟨(i, j)⟩`. Take `⟨⟨i0, j0⟩, hmax⟩` from `Finite.exists_max (fun p : n × n => ‖Y p.1 p.2‖)`.

Use `set t := ‖Y i0 j0‖ with ht`. Establish `hall : ∀ a b, ‖Y a b‖ ≤ t` using `fun a b => hmax (a, b)`. It suffices to establish `hs : t ≤ u ^ (k + 2) from (hall i j).trans hs`. Establish `t0 : 0 ≤ t` using `norm_nonneg _`. Establish `tsmall : t ≤ u ^ 2` using `e2 ▸ h1 i0 j0`.

Establish `u1 : u ≤ 1` using `by linarith`. Establish `t1 : t ≤ 1` using `tsmall.trans (pow_le_one₀ u0.le u1)`. Establish `hR` using `GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hall l i0 j0`. Establish `hX : (1 + Y) = X` using `by rw [hY]; abel`. Rewrite `hR` using `[hX]`.

Establish `key : ‖((l:ℚ_[l]) • Y) i0 j0‖ ≤ max (‖(X ^ l - 1) i0 j0‖) (t ^ 2)`. Establish `: ((l:ℚ_[l]) • Y) i0 j0 = (X ^ l - 1) i0 j0 - (X ^ l - 1 - (l:ℚ_[l]) • Y) i0 j0`. Simplify using `[Matrix.sub_apply]`. Rewrite using `[this]`. Establish `hu' : ∀ a b : ℚ_[l], ‖a - b‖ ≤ max ‖a‖ ‖b‖` using `fun a b => by`.

Rewrite using `[sub_eq_add_neg, ← norm_neg b]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Conclude with `(hu' _ _).trans (max_le_max le_rfl hR)`. Establish `hnorm : ‖((l:ℚ_[l]) • Y) i0 j0‖ = u * t`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p]`.

Rewrite `key` using `[hnorm]`. Break down `le_max_iff.mp key with h | h` into its components or cases. Establish `h' : u * t ≤ u * u ^ (k + 2)`. Rewrite using `[← pow_succ', ← e3]`. Conclude with `h.trans (h2 i0 j0)`.

Conclude with `le_of_mul_le_mul_left h' u0`. Break down `t0.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Check the signs of the components of the expression. It suffices to derive a contradiction.

Establish `: u ≤ t` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem matrix_near_one_pow_prime_deep : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) →
    (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) →
    ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l hl n _ _ X k h1 h2 i j
  have hL : (2:ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hLpos : (0:ℝ) < l := by linarith
  set u : ℝ := (l:ℝ)⁻¹ with hu
  have u0 : 0 < u := inv_pos.mpr hLpos
  have uhalf : u ≤ 1 / 2 := by
    rw [hu, one_div]; exact inv_anti₀ (by norm_num) hL
  have hz : ∀ m : ℕ, (l:ℝ) ^ (-(m:ℤ)) = u ^ m := fun m => by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have e2 : (l:ℝ) ^ (-2:ℤ) = u ^ 2 := hz 2
  have e3 : (l:ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = u ^ (k + 3) := by
    rw [← hz]; congr 1
  have e4 : (l:ℝ) ^ (-((k : ℤ) + 2)) = u ^ (k + 2) := by
    rw [← hz]; congr 1
  rw [e4]
  set Y := X - 1 with hY
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖Y p.1 p.2‖)
  set t := ‖Y i0 j0‖ with ht
  have hall : ∀ a b, ‖Y a b‖ ≤ t := fun a b => hmax (a, b)
  suffices hs : t ≤ u ^ (k + 2) from (hall i j).trans hs
  have t0 : 0 ≤ t := norm_nonneg _
  have tsmall : t ≤ u ^ 2 := e2 ▸ h1 i0 j0
  have u1 : u ≤ 1 := by linarith
  have t1 : t ≤ 1 := tsmall.trans (pow_le_one₀ u0.le u1)
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hall l i0 j0
  have hX : (1 + Y) = X := by rw [hY]; abel
  rw [hX] at hR
  have key : ‖((l:ℚ_[l]) • Y) i0 j0‖ ≤ max (‖(X ^ l - 1) i0 j0‖) (t ^ 2) := by
    have : ((l:ℚ_[l]) • Y) i0 j0 = (X ^ l - 1) i0 j0 - (X ^ l - 1 - (l:ℚ_[l]) • Y) i0 j0 := by
      simp [Matrix.sub_apply]
    rw [this]
    have hu' : ∀ a b : ℚ_[l], ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg, ← norm_neg b]; exact IsUltrametricDist.norm_add_le_max _ _
    exact (hu' _ _).trans (max_le_max le_rfl hR)
  have hnorm : ‖((l:ℚ_[l]) • Y) i0 j0‖ = u * t := by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p]
  rw [hnorm] at key
  rcases le_max_iff.mp key with h | h
  · have h' : u * t ≤ u * u ^ (k + 2) := by
      rw [← pow_succ', ← e3]; exact h.trans (h2 i0 j0)
    exact le_of_mul_le_mul_left h' u0
  · rcases t0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exfalso
      have : u ≤ t := by nlinarith
      nlinarith

end GlobalTheory
