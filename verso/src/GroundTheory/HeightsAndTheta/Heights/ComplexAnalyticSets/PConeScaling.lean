import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Pointwise

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_of_isHomogeneous {n i : ℕ} {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous i)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ i * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ j ∈ d.support, d j = i := by
    have h := hφ (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

attribute [local instance] MvPolynomial.gradedAlgebra in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem ConeScaling.proof : ConeScaling.Statement := by
  intro n J hJ t ht
  have key : ∀ s : ℂ, s • zeroSet J ⊆ zeroSet J := by
    rintro s _ ⟨x, hx, rfl⟩
    show ∀ q ∈ J, eval (s • x) q = 0
    intro q hq
    rw [← sum_homogeneousComponent q, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i q),
      hx _ (homogeneousComponent_mem_of_mem hJ hq i), mul_zero]
  refine (key t).antisymm fun x hx => ?_
  exact ⟨t⁻¹ • x, key _ (Set.smul_mem_smul_set hx), smul_inv_smul₀ ht x⟩

end GroundTheory.Heights₂.Heights.ComplexSets
