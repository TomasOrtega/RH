import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem degPoly_isBlockAlternating (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement)
    (d : IndexData) : RestTerms.IsBlockAlternating d.f d.N (degPoly d) := by
  intro w
  apply MvPolynomial.funext
  intro u
  have h := hAnti d w u
  rw [← hEval, ← hEval] at h
  rw [RestTerms.blockPermute, eval_rename, smul_eval]
  exact h

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem DelDividesDeg.proof (hAnti : DegAntisym.Statement) (hEval : DegPolyEval.Statement) :
    DelDividesDeg.Statement := fun d =>
  RestTerms.FlagVandermondeDvd.full d.f d.N (degPoly d) (degPoly_isBlockAlternating hAnti hEval d)

end GroundTheory.Heights₂.Heights.TheoremB
