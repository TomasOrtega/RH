import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) = monomial u (a * ∏ i, c i ^ u i)`. Rewrite using `[aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmon, coeff_monomial, coeff_monomial]`. Use `split_ifs with hue`. Substitute `hue` using the available equality. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Consider the case `add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
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
Establish `key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) = (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum, map_sum, map_pow, mul_pow, Finset.mul_sum]`. Conclude with `DFunLike.congr_fun key S`.
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
Introduce `N r k hk1 hkN nu s _ hnu hsum`. Take `⟨S₀, hS₀, hc₀⟩` from `h N r k hk1 hkN nu hnu hsum`. Use `⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]`. Rewrite using `[SchurSignCoefficient.coeff_aeval_diagonal, hc₀]`.

Use `congr 1`. Rewrite using `[Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]`. Rewrite using `[Finsupp.single_eq_same, pow_one]`. Use `congr 1`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hb), pow_zero]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.
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
