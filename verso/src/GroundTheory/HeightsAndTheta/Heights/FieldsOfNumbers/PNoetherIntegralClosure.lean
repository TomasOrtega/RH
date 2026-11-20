import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsNoetherIntegralClosure
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherReduction
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem NoetherIntegralClosureFinite.proof : NoetherIntegralClosureFinite.Statement := by
  intro k A _ _ _ _ _ K _ _ _ L _ _ _ _ _
  refine finite_integralClosure_of_forall_mvPolynomial k A K L fun s L' _ _ _ _ _ => ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_mvPolynomial_of_charP k p s L'
  · have : CharZero k := CharP.charP_to_charZero k
    exact finite_integralClosure_mvPolynomial_of_charZero k s L'

end GroundTheory.Heights₂.Heights.FieldNumbers
