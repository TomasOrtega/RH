import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
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
