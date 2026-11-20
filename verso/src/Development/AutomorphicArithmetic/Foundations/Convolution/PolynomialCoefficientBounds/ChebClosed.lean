import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Proceed by induction on `m using Nat.twoStepInduction with`. Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `more n h0 h1`. Establish `e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2` using `by push_cast; ring`.

Establish `e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1` using `by push_cast; ring`. Rewrite `h1` using `[e1]`. Rewrite using `[e, Polynomial.Chebyshev.T_add_two]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]`. Rewrite using `[h0, h1]`.

Take the linear combination `(-((y + s) ^ n + (y - s) ^ n) / 2) * hs`.
-/
private theorem UpperTheory.ConvolutionTheory.FX.cheb_closed (y s : ℝ) (hs : s ^ 2 = y ^ 2 - 1) (m : ℕ) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y = ((y + s) ^ m + (y - s) ^ m) / 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e1] at h1
    rw [e, Polynomial.Chebyshev.T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    rw [h0, h1]
    linear_combination (-((y + s) ^ n + (y - s) ^ n) / 2) * hs

/- English proof (translation)
Introduce `m y`. Use `⟨fun hy => ?_, fun hy => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `abs_le.mp hy`. Rewrite using `[← Real.cos_arccos h1 h2, Polynomial.Chebyshev.T_real_cos]`. Conclude with `Real.abs_cos_le_one _`.

Establish `h0 : 0 ≤ y ^ 2 - 1` using `by nlinarith`. Establish `hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1` using `Real.sq_sqrt h0`. Establish `hs0 : 0 ≤ Real.sqrt (y ^ 2 - 1)` using `Real.sqrt_nonneg _`. Establish `hsy : Real.sqrt (y ^ 2 - 1) ≤ y`. Apply `Real.sqrt_le_iff.mpr` to reduce the goal to its premises.

Apply the tactic sequence `constructor <;> linarith`. Establish `hc` using `UpperTheory.ConvolutionTheory.FX.cheb_closed y _ hs m`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Generalize the expression as in `Real.sqrt (y ^ 2 - 1) = s at *`.

Establish `ha : 0 ≤ y + s` using `by linarith`. Establish `hb : 0 ≤ y - s` using `by linarith`. Establish `pa : (y + s) ^ m ≤ (2 * y) ^ m` using `pow_le_pow_left₀ ha (by linarith) m`. Establish `pb : (y - s) ^ m ≤ (2 * y) ^ m` using `pow_le_pow_left₀ hb (by linarith) m`. Establish `qa` using `pow_nonneg ha m`.

Establish `qb` using `pow_nonneg hb m`. Rewrite using `[abs_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.ConvolutionTheory.FX.cheb_facts :
    ∀ (m : ℕ) (y : ℝ), (|y| ≤ 1 → |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y| ≤ 1) ∧ (1 ≤ y → (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y = ((y + Real.sqrt (y ^ 2 - 1)) ^ m + (y - Real.sqrt (y ^ 2 - 1)) ^ m) / 2 ∧ |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y| ≤ (2 * y) ^ m) := by
  intro m y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨h1, h2⟩ := abs_le.mp hy
    rw [← Real.cos_arccos h1 h2, Polynomial.Chebyshev.T_real_cos]
    exact Real.abs_cos_le_one _
  · have h0 : 0 ≤ y ^ 2 - 1 := by nlinarith
    have hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt h0
    have hs0 : 0 ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_nonneg _
    have hsy : Real.sqrt (y ^ 2 - 1) ≤ y := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> linarith
    have hc := UpperTheory.ConvolutionTheory.FX.cheb_closed y _ hs m
    refine ⟨hc, ?_⟩
    rw [hc]
    generalize Real.sqrt (y ^ 2 - 1) = s at *
    have ha : 0 ≤ y + s := by linarith
    have hb : 0 ≤ y - s := by linarith
    have pa : (y + s) ^ m ≤ (2 * y) ^ m := pow_le_pow_left₀ ha (by linarith) m
    have pb : (y - s) ^ m ≤ (2 * y) ^ m := pow_le_pow_left₀ hb (by linarith) m
    have qa := pow_nonneg ha m
    have qb := pow_nonneg hb m
    rw [abs_of_nonneg (by linarith)]
    linarith
