import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `rhsR recR horizPart vertPart intPart arInt`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : IsHorizontal W`.

Simplify using `[h]`. Simplify using `only [h, if_false, if_true, not_false_eq_true, zero_add, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem rhsR.equiv (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι)
    (A : HermLine ι) (s : MRing ι) : rhsR I P L A s = recR I P L A s := by
  classical
  unfold rhsR recR horizPart vertPart intPart arInt
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases h : IsHorizontal W
  · simp [h]
  · simp only [h, if_false, if_true, not_false_eq_true, zero_add, mul_assoc]
    rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
