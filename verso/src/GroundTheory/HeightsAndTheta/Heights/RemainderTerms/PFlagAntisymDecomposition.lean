import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

/- English proof (translation)
Simplify using `only [antisymmetrize, map_sum, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem antisymmetrize_finset_sum (f N : ℕ) {ι : Type*} (s : Finset ι) (g : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, g i) = ∑ i ∈ s, antisymmetrize f N (g i) := by
  simp only [antisymmetrize, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `f N F G Q R hF hR`. Rewrite using `[hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]`.
-/
theorem FlagAntisymDecomposition.proof (h1 : FlagSymmetricMulAntisym.Statement)
    (h2 : FlagPowerSumSymmetric.Statement) : FlagAntisymDecomposition.Statement := by
  intro f N F G Q R hF hR
  rw [hF, Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, antisymmetrize_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_left_comm, h1 f N _ _ (h2 f N l σ), hR, mul_left_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
