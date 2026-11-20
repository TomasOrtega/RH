import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]`. Establish `h` using `Finset.sum_range_reflect (fun i => i) m`. Rewrite using `[h, Finset.sum_range_id]`.
-/
theorem VandermondeOfHomogeneous.sum_card_Ioi (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℕ)) = m * (m - 1) / 2 := by
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]
  have h := Finset.sum_range_reflect (fun i => i) m
  rw [h, Finset.sum_range_id]

/- English proof (translation)
Introduce `σ R _ m v hv`. Rewrite using `[← VandermondeOfHomogeneous.sum_card_Ioi m]`. Unfold `vandermondeOf`. Use `IsHomogeneous.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Use `IsHomogeneous.prod _ _ _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `(hv i).sub (hv j)`.
-/
theorem VandermondeOfHomogeneous.proof : VandermondeOfHomogeneous.Statement := by
  intro σ R _ m v hv
  rw [← VandermondeOfHomogeneous.sum_card_Ioi m]
  unfold vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  exact (hv i).sub (hv j)

end GroundTheory.Heights₂.Heights.RestTerms
