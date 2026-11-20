import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Introduce `f N τ R`. Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C a => simp [restrictToBlock]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`.

Rewrite using `[map_mul, map_mul, map_mul, hp, constantCoeff_X, mul_zero]`. Establish `hX : constantCoeff (restrictToBlock f N τ (X i)) = 0`. Simplify using `only [restrictToBlock, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hX, mul_zero]`.
-/
theorem FlagRestrictConstantCoeff.proof : FlagRestrictConstantCoeff.Statement := by
  intro f N τ R
  induction R using MvPolynomial.induction_on with
  | C a => simp [restrictToBlock]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, constantCoeff_X, mul_zero]
    have hX : constantCoeff (restrictToBlock f N τ (X i)) = 0 := by
      simp only [restrictToBlock, aeval_X]
      split_ifs <;> simp
    rw [hX, mul_zero]

end RestTerms

end GroundTheory.Heights₂.Heights
