import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace PGaussTermBound

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem pow_le_sqrt_pow_mul_exp (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by
  set s := √(n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (s * ((m : ℝ) + 1)) (mul_nonneg hs.le hm) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at h1
  have hfac2 : (n.factorial : ℝ) ≤ s ^ n * s ^ n := by
    rw [← mul_pow, hss]
    exact_mod_cast Nat.factorial_le_pow n
  have hE : 0 ≤ Real.exp (s * ((m : ℝ) + 1)) := (Real.exp_pos _).le
  have h2 : s ^ n * ((m : ℝ) + 1) ^ n ≤ s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by
    rw [← mul_pow]
    calc (s * ((m : ℝ) + 1)) ^ n ≤ Real.exp (s * ((m : ℝ) + 1)) * (n.factorial : ℝ) := h1
      _ ≤ Real.exp (s * ((m : ℝ) + 1)) * (s ^ n * s ^ n) := mul_le_mul_of_nonneg_left hfac2 hE
      _ = s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by ring
  exact le_of_mul_le_mul_left h2 (pow_pos hs n)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem exponent_le (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by
  set s := √(n : ℝ) with hs_def
  have hss : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three

  have hA : s * m - π / 2 * (m : ℝ) ^ 2 ≤ n / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * m - s)]

  have hB : (m : ℝ) ≤ π / 2 * (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith

end PGaussTermBound

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem GaussTermBound.proof : GaussTermBound.Statement := by
  intro n hn m
  have h1 := PGaussTermBound.pow_le_sqrt_pow_mul_exp n m hn
  have h2 := PGaussTermBound.exponent_le n m
  have hE : 0 ≤ Real.exp (-π * (m : ℝ) ^ 2) := (Real.exp_pos _).le
  calc ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)
      ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) + n / (2 * π) + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
    _ = √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add]; ring

end GroundTheory.Heights₂.Heights
