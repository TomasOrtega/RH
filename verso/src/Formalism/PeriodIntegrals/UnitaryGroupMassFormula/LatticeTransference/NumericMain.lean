import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.GaussAbs

open Module
open scoped Real

namespace PI.Tr

/- English proof (translation)
Establish `hpi` using `Real.pi_gt_d2`. Establish `e1` using `Real.exp_one_gt_d9`. Establish `q1` using `Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.256 by norm_num)`. Establish `q2` using `Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.27 by norm_num)`. Establish `p1` using `Real.exp_pos 0.256`.

Establish `p2` using `Real.exp_pos 0.27`. Establish `hX : 3.5 < Real.exp (2 * π / 5)`. Establish `h : Real.exp 1.256 ≤ Real.exp (2 * π / 5)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `h' : Real.exp 1.256 = Real.exp 1 * Real.exp 0.256`. Rewrite using `[← Real.exp_add]`.

Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities. Establish `hY : 26 < Real.exp (25 * π / 24)`. Establish `h : Real.exp 3.27 ≤ Real.exp (25 * π / 24)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `h' : Real.exp 3.27 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 0.27`.

Rewrite using `[← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`. Evaluate the numerical expressions. Establish `e3 : 20 < Real.exp 1 * Real.exp 1 * Real.exp 1` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hXp : 0 < Real.exp (2 * π / 5)` using `Real.exp_pos _`.

Establish `hYp : 0 < Real.exp (25 * π / 24)` using `Real.exp_pos _`. Rewrite using `[Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]`. Establish `ha : 1 / Real.exp (2 * π / 5) < 2 / 7`. Rewrite using `[div_lt_iff₀ hXp]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hb : 1 / Real.exp (25 * π / 24) < 1 / 26`. Rewrite using `[div_lt_iff₀ hYp]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem numeric_main : 9 / 4 * Real.exp (-(2 * π / 5)) + 2 * (4 * Real.exp (-(25 * π / 24))) < 1 := by
  have hpi := Real.pi_gt_d2
  have e1 := Real.exp_one_gt_d9
  have q1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.256 by norm_num)
  have q2 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 0.27 by norm_num)
  have p1 := Real.exp_pos 0.256
  have p2 := Real.exp_pos 0.27
  have hX : 3.5 < Real.exp (2 * π / 5) := by
    have h : Real.exp 1.256 ≤ Real.exp (2 * π / 5) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 1.256 = Real.exp 1 * Real.exp 0.256 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hY : 26 < Real.exp (25 * π / 24) := by
    have h : Real.exp 3.27 ≤ Real.exp (25 * π / 24) := Real.exp_le_exp.mpr (by linarith)
    have h' : Real.exp 3.27 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 0.27 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have e3 : 20 < Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    nlinarith
  have hXp : 0 < Real.exp (2 * π / 5) := Real.exp_pos _
  have hYp : 0 < Real.exp (25 * π / 24) := Real.exp_pos _
  rw [Real.exp_neg, Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
  have ha : 1 / Real.exp (2 * π / 5) < 2 / 7 := by
    rw [div_lt_iff₀ hXp]; linarith
  have hb : 1 / Real.exp (25 * π / 24) < 1 / 26 := by
    rw [div_lt_iff₀ hYp]; linarith
  linarith

/- English proof (translation)
Establish `hb : 0 < τ⁻¹ * Real.exp (-κ)` using `by positivity`. Establish `key : Real.exp (-κ * m) * τ ^ (-m) = (τ⁻¹ * Real.exp (-κ)) ^ m`. Rewrite using `[Real.mul_rpow (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le, Real.inv_rpow hτ.le, ← Real.rpow_neg hτ.le, ← Real.exp_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem factor_le (κ τ m : ℝ) (hτ : 0 < τ) (hm : 1 ≤ m) (hh : τ⁻¹ * Real.exp (-κ) ≤ 1) :
    Real.exp (-κ * m) * τ ^ (-m) ≤ τ⁻¹ * Real.exp (-κ) := by
  have hb : 0 < τ⁻¹ * Real.exp (-κ) := by positivity
  have key : Real.exp (-κ * m) * τ ^ (-m) = (τ⁻¹ * Real.exp (-κ)) ^ m := by
    rw [Real.mul_rpow (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le, Real.inv_rpow hτ.le,
      ← Real.rpow_neg hτ.le, ← Real.exp_mul]
    ring
  rw [key]
  calc (τ⁻¹ * Real.exp (-κ)) ^ m ≤ (τ⁻¹ * Real.exp (-κ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb hh hm
    _ = τ⁻¹ * Real.exp (-κ) := Real.rpow_one _

/- English proof (translation)
Introduce `hP E _ _ _ Λ _ _ lam u hn hlam hdual`. Take `⟨sA, sQ, c, hc, PE⟩` from `hP E Λ`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `set n : ℝ := (finrank ℝ E : ℝ) with hndef`.

Establish `hn2 : (2 : ℝ) ≤ n` using `by rw [hndef]; exact_mod_cast hn`. Use `set m : ℝ := n / 2 with hmdef`. Establish `hm1 : 1 ≤ m` using `by rw [hmdef]; linarith`. Establish `hm0 : 0 < m` using `by linarith`. Use `set R2 : ℝ := (m / lam) ^ 2 with hR2`.

Use `set s : ℝ := 18 / 25 * lam ^ 2 / m with hsdef`. Establish `hs : 0 < s` using `by positivity`. Establish `hR : ∀ x : Λ, R2 ≤ ‖(x : E) + -u‖ ^ 2`. Introduce `x`. Establish `h` using `hcon x x.2`.

Establish `h' : m / lam < ‖(x : E) + -u‖`. Rewrite using `[div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]`. Rewrite using `[hmdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hR2]`.

Conclude with `pow_le_pow_left₀ (by positivity) h'.le 2`. Establish `hl : ∀ y : dualLat Λ, ‖(y : E)‖ ^ 2 < lam ^ 2 → Real.cos (2 * π * inner ℝ (y : E) (-u)) = 1`. Introduce `y hy`. Establish `hy' : ‖(y : E)‖ < lam`. Use polynomial arithmetic with `[norm_nonneg (y : E)]`.

Take `⟨k, hk⟩` from `hdual y (fun x hx => y.2 x hx) hy'`. Rewrite using `[inner_neg_right, real_inner_comm, hk]`. Establish `: 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π)` using `by push_cast; ring`. Rewrite using `[this, Real.cos_int_mul_two_pi]`. Establish `key` using `gauss_abstract (X := Λ) (Y := dualLat Λ) (fun x => ‖(x : E) + -u‖ ^ 2) (fun x => ‖(x : E) + 0‖ ^ 2) (fun y => ‖(y : E)‖ ^ 2) (fun y => Real.cos (2 * π * inner ℝ (y : E) (-u))) n c (fun y => sq_nonneg _) (fun x => sq_nonneg _) (fun y => Real.abs_cos_le_one _) hc 0 (fun t ht => sA …`.

Rewrite using `[PE t ht 0]`. Simplify using `only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])`. Use `R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)`. Establish `hlam0 : lam ≠ 0` using `hlam.ne'`. Establish `hm0' : m ≠ 0` using `hm0.ne'`.

Establish `e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m`. Rewrite using `[hsdef, hR2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m`.

Rewrite using `[hsdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : -n / 2 = -m` using `by rw [hmdef]; ring`. Rewrite `key` using `[e1, e2, e3]`.

Establish `hN` using `numeric_main`. Establish `hA : 0 < Real.exp (-(2 * π / 5))` using `Real.exp_pos _`. Establish `hB : 0 < Real.exp (-(25 * π / 24))` using `Real.exp_pos _`. Establish `f1` using `factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by`. Rewrite using `[show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)`.

Establish `f2` using `factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by`. Rewrite using `[show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)`. Rewrite `f1` using `[show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]`. Rewrite `f2` using `[show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gaussStep : GaussStep := by
  intro hP E _ _ _ Λ _ _ lam u hn hlam hdual
  obtain ⟨sA, sQ, c, hc, PE⟩ := hP E Λ
  by_contra hcon
  push_neg at hcon
  set n : ℝ := (finrank ℝ E : ℝ) with hndef
  have hn2 : (2 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  set m : ℝ := n / 2 with hmdef
  have hm1 : 1 ≤ m := by rw [hmdef]; linarith
  have hm0 : 0 < m := by linarith
  set R2 : ℝ := (m / lam) ^ 2 with hR2
  set s : ℝ := 18 / 25 * lam ^ 2 / m with hsdef
  have hs : 0 < s := by positivity
  have hR : ∀ x : Λ, R2 ≤ ‖(x : E) + -u‖ ^ 2 := by
    intro x
    have h := hcon x x.2
    have h' : m / lam < ‖(x : E) + -u‖ := by
      rw [div_lt_iff₀ hlam, ← sub_eq_add_neg, norm_sub_rev]
      rw [hmdef]; linarith
    rw [hR2]
    exact pow_le_pow_left₀ (by positivity) h'.le 2
  have hl : ∀ y : dualLat Λ, ‖(y : E)‖ ^ 2 < lam ^ 2 →
      Real.cos (2 * π * inner ℝ (y : E) (-u)) = 1 := by
    intro y hy
    have hy' : ‖(y : E)‖ < lam := by
      nlinarith [norm_nonneg (y : E)]
    obtain ⟨k, hk⟩ := hdual y (fun x hx => y.2 x hx) hy'
    rw [inner_neg_right, real_inner_comm, hk]
    have : 2 * π * -(k : ℝ) = ((-k : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_int_mul_two_pi]
  have key := gauss_abstract (X := Λ) (Y := dualLat Λ) (fun x => ‖(x : E) + -u‖ ^ 2)
    (fun x => ‖(x : E) + 0‖ ^ 2) (fun y => ‖(y : E)‖ ^ 2)
    (fun y => Real.cos (2 * π * inner ℝ (y : E) (-u))) n c
    (fun y => sq_nonneg _) (fun x => sq_nonneg _) (fun y => Real.abs_cos_le_one _) hc 0
    (fun t ht => sA t ht (-u)) (fun t ht => sA t ht 0) (fun t ht => sQ t ht)
    (fun t ht => PE t ht (-u))
    (fun t ht => by
      rw [PE t ht 0]
      simp only [inner_zero_right, mul_zero, Real.cos_zero, mul_one])
    R2 (lam ^ 2) hR hl s (4 / 9) (1 / 4) hs (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  have e1 : -π * s * (1 - 4 / 9) * R2 = -(2 * π / 5) * m := by
    rw [hsdef, hR2]; field_simp; ring
  have e2 : -π * (1 - 1 / 4) * lam ^ 2 / s = -(25 * π / 24) * m := by
    rw [hsdef]; field_simp; ring
  have e3 : -n / 2 = -m := by rw [hmdef]; ring
  rw [e1, e2, e3] at key
  have hN := numeric_main
  have hA : 0 < Real.exp (-(2 * π / 5)) := Real.exp_pos _
  have hB : 0 < Real.exp (-(25 * π / 24)) := Real.exp_pos _
  have f1 := factor_le (2 * π / 5) (4 / 9) m (by norm_num) hm1 (by
    rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num]; linarith)
  have f2 := factor_le (25 * π / 24) (1 / 4) m (by norm_num) hm1 (by
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num]; linarith)
  rw [show ((4 : ℝ) / 9)⁻¹ = 9 / 4 by norm_num] at f1
  rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at f2
  linarith

end PI.Tr
