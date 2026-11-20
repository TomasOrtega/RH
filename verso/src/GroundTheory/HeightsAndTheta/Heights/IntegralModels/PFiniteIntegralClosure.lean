import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharP
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
Introduce `A _ _ _ K _ _ _ L _ _ _ _ _`. Take `⟨p, hp⟩` from `CharP.exists A`. Break down `CharP.char_is_prime_or_zero A p with hp' | rfl` into its components or cases. Establish `: Fact p.Prime` using `⟨hp'⟩`. Conclude with `finite_integralClosure_of_charP p A K L`.

Establish `: CharZero A` using `CharP.charP_to_charZero A`. Conclude with `finite_integralClosure_of_charZero A K L`.
-/
theorem FiniteIntegralClosure.proof : FiniteIntegralClosure.Statement := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists A
  rcases CharP.char_is_prime_or_zero A p with hp' | rfl
  · have : Fact p.Prime := ⟨hp'⟩
    exact finite_integralClosure_of_charP p A K L
  · have : CharZero A := CharP.charP_to_charZero A
    exact finite_integralClosure_of_charZero A K L

end GroundTheory.Heights₂.Heights.Model
