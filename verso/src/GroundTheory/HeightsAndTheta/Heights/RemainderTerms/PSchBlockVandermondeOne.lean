import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms
