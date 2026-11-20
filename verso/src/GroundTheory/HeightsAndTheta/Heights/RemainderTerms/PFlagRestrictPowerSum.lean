import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem FlagRestrictPowerSum.proof : FlagRestrictPowerSum.Statement := by
  intro f N k τ σ hk
  have hk0 : k ≠ 0 := by omega
  unfold blockPowerSum restrictToBlock
  simp only [map_sum, map_pow, aeval_X]
  split_ifs with h
  · subst h
    simp [psum]
  · simp [zero_pow hk0]

end RestTerms

end GroundTheory.Heights₂.Heights
