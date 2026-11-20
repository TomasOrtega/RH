import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Introduce `f N H`. Take `⟨R, hR⟩` from `h1 f N _ (isBlockAlternating_antisymmetrize f N H)`. Use `⟨R, hR, fun w => ?_⟩` and prove the remaining obligations. Establish `h` using `isBlockAlternating_antisymmetrize f N H w`. Rewrite `h` using `[hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc]`.

Establish `hs : blockSign f N w ≠ 0`. Introduce `h0`. Use `Flag.blockSign_mul_self f N w` as an intermediate fact. Rewrite `this` using `[h0, zero_mul]`. Conclude with `zero_ne_one this`.

Conclude with `mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)`.
-/
theorem FlagDividedDifferencePoly.proof (h1 : FlagVandermondeDvd.Statement) :
    FlagDividedDifferencePoly.Statement := by
  intro f N H
  obtain ⟨R, hR⟩ := h1 f N _ (isBlockAlternating_antisymmetrize f N H)
  refine ⟨R, hR, fun w => ?_⟩
  have h := isBlockAlternating_antisymmetrize f N H w
  rw [hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc] at h
  have hs : blockSign f N w ≠ 0 := by
    intro h0
    have := Flag.blockSign_mul_self f N w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)

end RestTerms

end GroundTheory.Heights₂.Heights
