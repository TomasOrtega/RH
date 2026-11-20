import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem VandermondeOfHomogeneous.sum_card_Ioi (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℕ)) = m * (m - 1) / 2 := by
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]
  have h := Finset.sum_range_reflect (fun i => i) m
  rw [h, Finset.sum_range_id]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem VandermondeOfHomogeneous.proof : VandermondeOfHomogeneous.Statement := by
  intro σ R _ m v hv
  rw [← VandermondeOfHomogeneous.sum_card_Ioi m]
  unfold vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  exact (hv i).sub (hv j)

end GroundTheory.Heights₂.Heights.RestTerms
