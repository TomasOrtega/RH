import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
