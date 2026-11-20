import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

/- English proof (translation)
Introduce `f N τ R k hR`. Establish `h` using `hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by`. Introduce `p`. Use `split_ifs`. Conclude with `isHomogeneous_X ℚ _`.

Conclude with `isHomogeneous_zero _ _ _)`. Rewrite `h` using `[one_mul]`. Conclude with `h`.
-/
theorem FlagRestrictHomogeneous.proof : FlagRestrictHomogeneous.Statement := by
  intro f N τ R k hR
  have h := hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by
    intro p
    split_ifs
    · exact isHomogeneous_X ℚ _
    · exact isHomogeneous_zero _ _ _)
  rw [one_mul] at h
  exact h

end GroundTheory.Heights₂.Heights.RestTerms
