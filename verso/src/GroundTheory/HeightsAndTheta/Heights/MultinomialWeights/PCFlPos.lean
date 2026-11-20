import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_polarPoly {σ R : Type*} [CommRing R] [Fintype σ] (Φ : MvPolynomial σ R →ₗ[R] R)
    (n : ℕ) (m : σ →₀ ℕ) : coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  unfold polarPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem coeff_neg_outerDot_pow (σ : Type*) [Fintype σ] (m : σ →₀ ℕ) (n : ℕ) :
    coeff m ((-outerDot σ ℚ) ^ n) =
      if m.sum (fun _ e => e) = n then monomial m ((-1) ^ n * (m.multinomial : ℚ)) else 0 := by
  have hdot : outerDot σ ℚ =
      ∑ v, (X v : MvPolynomial σ ℚ) • (X v : MvPolynomial σ (MvPolynomial σ ℚ)) := by
    unfold outerDot
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_eq_C_mul, mul_comm]
  have hneg : (-outerDot σ ℚ) ^ n = C ((-1) ^ n) * outerDot σ ℚ ^ n := by
    rw [show (C ((-1 : MvPolynomial σ ℚ) ^ n) : MvPolynomial σ (MvPolynomial σ ℚ)) = (-1) ^ n by
      simp]
    exact neg_pow (outerDot σ ℚ) n
  rw [hneg, coeff_C_mul, hdot, coeff_linearCombination_X_pow_of_fintype]
  split_ifs with h
  · rw [monomial_eq, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  · rw [mul_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagIntegral_monomial (f N : ℕ) (m : Fin f × Fin N →₀ ℕ) :
    RestTerms.flagIntegral f N (monomial m 1) =
      coeff m (RestTerms.blockVandermonde f N) * m.prod (fun _ e => (e.factorial : ℚ)) := by
  classical
  unfold RestTerms.flagIntegral
  rw [Finset.sum_eq_single m]
  · rw [coeff_monomial, if_pos rfl, one_mul]
  · intro b _ hb
    rw [coeff_monomial, if_neg (Ne.symm hb), zero_mul, zero_mul]
  · intro hm
    rw [MvPolynomial.notMem_support_iff.mp hm, coeff_monomial, if_pos rfl]
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify by unfolding definitions. A detailed English derivation is pending.
-/
theorem prod_factorial_mul_multinomial {σ : Type*} (m : σ →₀ ℕ) :
    (m.prod (fun _ e => (e.factorial : ℚ))) * (m.multinomial : ℚ) =
      ((m.sum fun _ e => e).factorial : ℚ) := by
  rw [Finsupp.multinomial_eq]
  have := Nat.multinomial_spec m.support m
  unfold Finsupp.prod Finsupp.sum
  dsimp only
  exact_mod_cast this

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem degPoly_eq (d : IndexData) :
    degPoly d = C (((d.D).factorial : ℚ) / (∏ i : Fin d.N, ((i : ℕ).factorial : ℚ)) ^ d.f) *
      RestTerms.blockVandermonde d.f d.N := by
  ext m
  rw [coeff_C_mul, degPoly, coeff_polarPoly, coeff_neg_outerDot_pow]
  split_ifs with h
  · rw [← mul_one ((-1) ^ d.D * (m.multinomial : ℚ)), ← smul_eq_mul, ← smul_monomial,
      map_smul, intFl, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    change _ * (flagNormalisation d.f d.N * RestTerms.flagIntegral d.f d.N (monomial m 1)) = _
    rw [flagIntegral_monomial, flagNormalisation]
    have hf := prod_factorial_mul_multinomial m
    rw [h] at hf
    have hD : d.D = RestTerms.topDegree d.f d.N := rfl
    rw [← hf, ← hD]
    have hP : (∏ i : Fin d.N, ((i : ℕ).factorial : ℚ)) ^ d.f ≠ 0 := by positivity
    field_simp
    have h1 : ((-1 : ℚ) ^ d.D) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h1, one_mul]
  · rw [map_zero]
    have hom := RestTerms.FlagVandermondeHomogeneous.proof d.f d.N
    rw [hom.coeff_eq_zero, mul_zero]
    intro hdeg
    apply h
    change _ = RestTerms.topDegree _ _
    rw [← hdeg]
    rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem CFlPos.proof : CFlPos.Statement := fun d =>
  ⟨_, by positivity, degPoly_eq d⟩

end GroundTheory.Heights₂.Heights.TheoremB
