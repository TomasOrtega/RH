import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `f N F Q d hF hFh hNd`. Unfold `RestTerms.IsPowerSumDecomposition at hF ⊢`. Establish `h` using `congrArg (homogeneousComponent d) hF`. Rewrite `h` using `[homogeneousComponent_eq_self hFh]`. Rewrite using `[h, map_sum]`.

Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hlN : l ≤ N` using `(Finset.mem_Icc.mp hl).2`. Establish `hp : (RestTerms.blockPowerSum f N l τ).IsHomogeneous l`.

Unfold `RestTerms.blockPowerSum`. Conclude with `IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _`. Rewrite using `[KRest.homogeneousComponent_mul_left hp, if_pos (hlN.trans hNd)]`.
-/
theorem RestCutHomDecomp.proof : RestCutHomDecomp.Statement := by
  intro f N F Q d hF hFh hNd
  unfold RestTerms.IsPowerSumDecomposition at hF ⊢
  have h := congrArg (homogeneousComponent d) hF
  rw [homogeneousComponent_eq_self hFh] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlN : l ≤ N := (Finset.mem_Icc.mp hl).2
  have hp : (RestTerms.blockPowerSum f N l τ).IsHomogeneous l := by
    unfold RestTerms.blockPowerSum
    exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  rw [KRest.homogeneousComponent_mul_left hp, if_pos (hlN.trans hNd)]

end GroundTheory.Heights₂.Heights
