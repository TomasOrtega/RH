import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem RestBound.proof (h₁ : RestPrimeBound.Statement) (h₂ : RestBoundOfPrimeBound.Statement) :
    RestBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  refine ⟨(h₁ f r a c B₀ hf hr ha hB).1, ?_⟩
  intro Q hQ s e he P
  exact h₂ f r a c B₀ hf hr ha hB Q s e
    (fun p hp hpB => (h₁ f r a c B₀ hf hr ha hB).2 Q hQ s e he p hp hpB) P

end RestTerms

end GroundTheory.Heights₂.Heights
