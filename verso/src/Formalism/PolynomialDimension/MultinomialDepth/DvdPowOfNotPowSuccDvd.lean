import Formalism.PolynomialDimension.EdgeSumGoodRank

noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation.
-/
theorem one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by
  classical
  have hP : ∀ t : Finset ι, 1 - ∑ j ∈ t, κ j ≤ ∏ j ∈ t, (1 - κ j) := by
    intro t
    refine Finset.induction_on t (by simp) ?_
    intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ 1 - κ i := by linarith [(hκ i).2]
    have h2 : 0 ≤ ∑ j ∈ t, κ j := Finset.sum_nonneg fun j _ => (hκ j).1
    have h3 := mul_le_mul_of_nonneg_left ih h1
    nlinarith [mul_nonneg (hκ i).1 h2]
  have hd0 : 0 ≤ ∏ j ∈ s, d j := Finset.prod_nonneg fun j _ => hd j
  calc (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ (∏ j ∈ s, (1 - κ j)) * ∏ j ∈ s, d j :=
        mul_le_mul_of_nonneg_right (hP s) hd0
    _ = ∏ j ∈ s, ((1 - κ j) * d j) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ j ∈ s, n j := Finset.prod_le_prod
        (fun j _ => mul_nonneg (by linarith [(hκ j).2]) (hd j)) (fun j _ => h j)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem share_product_bound : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h

section Partner

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Partner

end Formalism.CountingSumsFrames
