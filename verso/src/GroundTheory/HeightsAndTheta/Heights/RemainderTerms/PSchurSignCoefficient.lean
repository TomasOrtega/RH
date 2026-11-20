import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Treat this case separately. A detailed English derivation is pending.
-/
theorem SchurSignCoefficient.coeff_aeval_diagonal {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    coeff e (aeval (fun i : Fin N => C (c i) * X i) P) = (∏ i, c i ^ e i) * coeff e P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) =
        monomial u (a * ∏ i, c i ^ u i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hue
    · subst hue; ring
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem SchurSignCoefficient.aeval_smul_powerSumHom (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by
  have key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) =
      (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum,
      map_sum, map_pow, mul_pow, Finset.mul_sum]
  exact DFunLike.congr_fun key S

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem SchurSignCoefficient.proof (h : SchurPowerSumCoefficient.Statement) :
    SchurSignCoefficient.Statement := by
  intro N r k hk1 hkN nu s _ hnu hsum
  obtain ⟨S₀, hS₀, hc₀⟩ := h N r k hk1 hkN nu hnu hsum
  refine ⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩
  · rw [← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]
  · rw [SchurSignCoefficient.coeff_aeval_diagonal, hc₀]
    congr 1
    rw [Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]
    · rw [Finsupp.single_eq_same, pow_one]
      congr 1
      simp only
      omega
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg (Ne.symm hb), pow_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

end

end RestTerms

end GroundTheory.Heights₂.Heights
