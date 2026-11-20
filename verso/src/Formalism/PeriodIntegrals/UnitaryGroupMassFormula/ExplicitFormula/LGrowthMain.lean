import Mathlib
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthDefs

noncomputable section

namespace PI.EF

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Establish `hre : 0 < w.re` using `by linarith`. Establish `hb` using `hB N χ hχ1 w hre`. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)`. Establish `ht` using `abs_nonneg w.im`. Establish `hw : ‖w‖ ≤ 8 + |w.im|`.

Use `(Complex.norm_le_abs_re_add_abs_im w).trans ?_` and prove the remaining obligations. Rewrite using `[abs_of_pos hre]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|)`. Rewrite using `[div_le_iff₀ hre]`.

Use polynomial arithmetic with `[norm_nonneg w]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem L_right (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 8) :
    ‖LFunction χ w‖ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by
  have hre : 0 < w.re := by linarith
  have hb := hB N χ hχ1 w hre
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg w.im
  have hw : ‖w‖ ≤ 8 + |w.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|) := by
    rw [div_le_iff₀ hre]
    nlinarith [norm_nonneg w]
  calc ‖LFunction χ w‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + ‖w‖ / w.re) := hb
    _ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 2 * (8 + |w.im|)) := by gcongr
    _ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by nlinarith

/- English proof (translation)
Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)`. Establish `ht` using `abs_nonneg s.im`. Establish `hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2)` using `one_le_mul_of_one_le_of_one_le hN (by linarith)`. Distinguish the cases in `hr : 1 / 2 ≤ s.re`. Combine the equalities or inequalities in the displayed calculation.

Establish `: (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7` using `le_self_pow₀ hX (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Use `push_neg at hr`. Establish `h0 : χ 0 = 0`. Distinguish the cases in `hN1 : N = 1`.

Substitute `hN1` using the available equality. It suffices to derive a contradiction. Apply `hχ1` to reduce the goal to its premises. Conclude with `MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp`. Use `haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1`.

Conclude with `χ.map_nonunit not_isUnit_zero`. Establish `hw1 : 1 / 2 ≤ (1 - s).re` using `by simp only [Complex.sub_re, Complex.one_re]; linarith`. Establish `hw2 : (1 - s).re ≤ 5` using `by simp only [Complex.sub_re, Complex.one_re]; linarith`. Establish `hL1` using `norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)`. Rewrite `hL1` using `[sub_sub_cancel]`.

Establish `hinv : χ⁻¹ ≠ 1` using `inv_ne_one.2 hχ1`. Establish `hL2` using `L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)`. Establish `hwim : |(1 - s).im| = |s.im|` using `by simp`. Rewrite `hL2` using `[hwim]`. Establish `hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im|`.

Use `(Complex.norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations. Establish `e : |(1 - s + 1).im| = |s.im|` using `by simp`. Establish `e2 : (1 - s + 1).re = (1 - s).re + 1` using `by simp`. Rewrite using `[e, e2, abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring`. Use `_ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)`.
-/
theorem L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg s.im
  have hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := one_le_mul_of_one_le_of_one_le hN (by linarith)
  by_cases hr : 1 / 2 ≤ s.re
  · calc ‖LFunction χ s‖ ≤ 37 * ((N : ℝ) * (|s.im| + 2)) := L_right hB hχ1 hr h2
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
        have : (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7 := le_self_pow₀ hX (by norm_num)
        nlinarith
  · push_neg at hr
    have h0 : χ 0 = 0 := by
      by_cases hN1 : N = 1
      · subst hN1
        exfalso
        apply hχ1
        exact MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp
      · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
        exact χ.map_nonunit not_isUnit_zero
    have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hL1 := norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)
    rw [sub_sub_cancel] at hL1
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
    have hL2 := L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hwim : |(1 - s).im| = |s.im| := by simp
    rw [hwim] at hL2
    have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e : |(1 - s + 1).im| = |s.im| := by simp
      have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
      rw [e, e2, abs_of_pos (by linarith)]
      linarith
    calc ‖LFunction χ s‖ ≤ 6 * (N : ℝ) ^ 5 * ‖1 - s + 1‖ ^ 5 * ‖LFunction χ⁻¹ (1 - s)‖ := hL1
      _ ≤ 6 * (N : ℝ) ^ 5 * (6 + |s.im|) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 5 * (3 * (|s.im| + 2)) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by
          gcongr
          linarith
      _ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)

/- English proof (translation)
Introduce `N _ χ hχ s h1 h2`. Establish `e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ)` using `fun x => by`. Rewrite using `[show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite using `[e7]`. Distinguish the cases in `hc : χ = 1`.

Substitute `hc` using the available equality. Establish `hN : N = 1`. Establish `h0` using `hχ`. Rewrite `h0` using `[DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one]`. Conclude with `h0.symm`.

Substitute `hN` using the available equality. Simplify using `only [del1, ↓reduceIte, one_mul]`. Rewrite using `[show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]`. Use `le_trans (hZ s h1 h2) ?_` and prove the remaining obligations. Simplify using `only [Nat.cast_one, one_mul]`.

Use `gcongr`. Conclude with `le_max_left _ _`. Simplify using `only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_max_right _ _`.
-/
theorem lGrowth_of (hB : PI.LBoundRight) {C : ℝ} (hZ : ZetaGrowth C) :
    LGrowth 7 (max C 53946) := by
  intro N _ χ hχ s h1 h2
  have e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ) := fun x => by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e7]
  by_cases hc : χ = 1
  · subst hc
    have hN : N = 1 := by
      have h0 := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h0
      exact h0.symm
    subst hN
    simp only [del1, ↓reduceIte, one_mul]
    rw [show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]
    refine le_trans (hZ s h1 h2) ?_
    simp only [Nat.cast_one, one_mul]
    gcongr
    exact le_max_left _ _
  · simp only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]
    calc ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := L_nontriv_growth hB hχ hc h1 h2
      _ ≤ max C 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
          gcongr
          exact le_max_right _ _

end PI.EF
