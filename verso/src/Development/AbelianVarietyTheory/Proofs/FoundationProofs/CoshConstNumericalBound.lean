import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (p + q) with h0 | hpos` into its components or cases. Establish `hp : p = 0` using `by omega`. Establish `hq : q = 0` using `by omega`. Substitute `hp hq` using the available equality. Simplify using the standard rewrite rules.

Establish `hsq : (p + q) ^ 2 = (p ^ 2 + q ^ 2) + 2 * (p * q)` using `by ring`. Establish `hmin : 2 * (p + q) * min p q ≤ 4 * (p * q)`. Break down `le_total p q with h | h` into its components or cases. Rewrite using `[min_eq_left h]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[min_eq_right h]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hR : Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) = (((p + q : ℕ) : ℝ) + 2) ^ (3 * (p + q) ^ 2)`. Establish `: (3 * ((p + q : ℕ) : ℝ) ^ 2) = ((3 * (p + q) ^ 2 : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite using `[this, Real.exp_nat_mul, Real.exp_log (by positivity)]`.

Rewrite using `[hR, hsq]`. Establish `ha : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ)` using `by exact_mod_cast hpos`. Generalize the expression as in `((p + q : ℕ) : ℝ) = a at ha`. Generalize the expression as in `p ^ 2 + q ^ 2 = d`. Generalize the expression as in `2 * (p + q) * min p q = m at hmin`.

Generalize the expression as in `p * q = n at hmin`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hpi` using `Real.pi_pos`. Establish `hmax : max 1 (3 / 2 * a ^ 2) = 3 / 2 * a ^ 2` using `max_eq_right (by nlinarith)`. Establish `h1 : 18 / 5 * (3 / 2 * a ^ 2) / a = 27 / 5 * a` using `by field_simp; ring`.

Establish `h2 : 2 * Real.pi / (2 / ((a + 1) / 2)) ^ 2 = Real.pi * ((a + 1) ^ 2 / 8)` using `by field_simp; ring`. Rewrite using `[hmax, h1, h2]`. Establish `h3 : (2 : ℝ) ^ m ≤ 16 ^ n`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 27 / 5 * a * (9 / 2) ≤ (a + 2) ^ 3`.

Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ a + 8 by linarith)]`. Establish `h5 : 8 * a * (a + 1) ≤ (a + 2) ^ 3`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (a - 1)) ha0.le]`. Establish `h6 : (27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8) ≤ (a + 2) ^ 6`. Establish `h7 : (8 * a * (a + 1)) ^ 2 ≤ ((a + 2) ^ 3) ^ 2` using `by gcongr`.

Establish `h8 : 0 ≤ (a * (a + 1)) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_add, pow_mul, mul_pow Real.pi, mul_pow (27 / 5 * a) (9 / 2), mul_pow _ ((a + 1) ^ 2 / 8), mul_pow _ (16 : ℝ)]`. Clear the denominators using the available nonvanishing facts.

Use `_ ≤ ((a + 2) ^ 3) ^ d * ((a + 2) ^ 6) ^ n := by gcongr`. Use `_ = (a + 2) ^ (3 * (d + 2 * n)) := by`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cosh_const_numerical_bound (p q : ℕ) :
    (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    simp
  have hsq : (p + q) ^ 2 = (p ^ 2 + q ^ 2) + 2 * (p * q) := by ring
  have hmin : 2 * (p + q) * min p q ≤ 4 * (p * q) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hR : Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2))
      = (((p + q : ℕ) : ℝ) + 2) ^ (3 * (p + q) ^ 2) := by
    have : (3 * ((p + q : ℕ) : ℝ) ^ 2) = ((3 * (p + q) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hR, hsq]
  have ha : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpos
  generalize ((p + q : ℕ) : ℝ) = a at ha
  generalize p ^ 2 + q ^ 2 = d
  generalize 2 * (p + q) * min p q = m at hmin
  generalize p * q = n at hmin
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_pos
  have hmax : max 1 (3 / 2 * a ^ 2) = 3 / 2 * a ^ 2 := max_eq_right (by nlinarith)
  have h1 : 18 / 5 * (3 / 2 * a ^ 2) / a = 27 / 5 * a := by field_simp; ring
  have h2 : 2 * Real.pi / (2 / ((a + 1) / 2)) ^ 2 = Real.pi * ((a + 1) ^ 2 / 8) := by
    field_simp; ring
  rw [hmax, h1, h2]
  have h3 : (2 : ℝ) ^ m ≤ 16 ^ n := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) hmin
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have h4 : 27 / 5 * a * (9 / 2) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ a + 8 by linarith)]
  have h5 : 8 * a * (a + 1) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) ha0.le]
  have h6 : (27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8) ≤ (a + 2) ^ 6 := by
    have h7 : (8 * a * (a + 1)) ^ 2 ≤ ((a + 2) ^ 3) ^ 2 := by gcongr
    have h8 : 0 ≤ (a * (a + 1)) ^ 2 := by positivity
    nlinarith
  calc (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (2 ^ m * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n)
      ≤ (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (16 ^ n * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n) := by gcongr
    _ = (27 / 5 * a * (9 / 2)) ^ d * ((27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8)) ^ n := by
        rw [pow_add, pow_mul, mul_pow Real.pi, mul_pow (27 / 5 * a) (9 / 2),
          mul_pow _ ((a + 1) ^ 2 / 8), mul_pow _ (16 : ℝ)]
        field_simp
    _ ≤ ((a + 2) ^ 3) ^ d * ((a + 2) ^ 6) ^ n := by gcongr
    _ = (a + 2) ^ (3 * (d + 2 * n)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

end GlobalTheory.CartanInt
