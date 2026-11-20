import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Evaluate the numerical expressions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
