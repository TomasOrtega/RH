import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lowMul_upU_leadMinor_ne_zero (K : Type) [Field K] (s : ℕ) (y : Low s → K) (b : Matrix (Fin s) (Fin s) K) (hb : ∀ i j, i < j → b i j = 0) (hdet : b.det ≠ 0) :
    (upU y).det = 1 ∧ ∀ k : ℕ, ((b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 := by
  have hU : ∀ a c : Fin s, c < a → upU y a c = 0 := by
    intro a c h
    simp [upU, Matrix.of_apply, not_lt.mpr h.le, h.ne']
  have hUd : ∀ a : Fin s, upU y a a = 1 := by
    intro a; simp [upU, Matrix.of_apply]
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h1 : b.det = ∏ i, b i i := Matrix.det_of_lowerTriangular b (fun i j h => hb i j h)
    rw [h1] at hdet
    intro i
    exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular (fun a c h => hU a c h)]
    simp [hUd]
  · intro k
    have hmul : (b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
          (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) =
        b.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) *
          (upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
            (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < k)]
      have h0 : ∑ l : {a : Fin s // ¬ (a : ℕ) < k}, b i.1 l.1 * upU y l.1 j.1 = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have : i.1 < l.1 := by
          have := i.2; have := l.2; rw [Fin.lt_iff_val_lt_val]; omega
        rw [hb _ _ this, zero_mul]
      rw [h0, add_zero]
    rw [hmul, Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => hb i.1 j.1 h)]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i.1)
    · rw [Matrix.det_of_upperTriangular (fun i j h => hU i.1 j.1 h)]
      simp [hUd]

end GlobalTheory.FlagCell2
