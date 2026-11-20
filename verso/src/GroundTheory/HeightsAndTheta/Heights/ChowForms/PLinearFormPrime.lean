import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem linearForm_coeff_single {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem LinearFormPrime.proof : LinearFormPrime.Statement := by
  intro F _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)
  · apply le_antisymm
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
    · have hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support := by
        rw [mem_support_iff, linearForm_coeff_single]
        exact hi
      simpa using le_totalDegree hs
  · intro x hx
    have h := hx (Finsupp.single i 1)
    rw [linearForm_coeff_single] at h
    refine isUnit_iff_ne_zero.mpr ?_
    rintro rfl
    exact hi (zero_dvd_iff.mp h)

end

end GroundTheory.Heights₂.Heights
