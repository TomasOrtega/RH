import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

/- English proof (translation)
Introduce `f N P H hP`. Unfold `antisymmetrize`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hP w, mul_smul_comm]`.
-/
theorem FlagSymmetricMulAntisym.proof : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]

end RestTerms

end GroundTheory.Heights₂.Heights
