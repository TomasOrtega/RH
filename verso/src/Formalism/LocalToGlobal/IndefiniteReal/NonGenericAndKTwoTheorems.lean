import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement

namespace Formalism.IndefR.NonGenericAndKTwoTheorems

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef Formalism.IndefR.HeckeTupleConditions

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Fix the arbitrary inputs or assume the hypotheses. Prove the second alternative.

A detailed English derivation is pending.
-/
theorem hecke_tuple_condition : UntwistedOfSupportAtTwistedPlaces := by
  intro K _ _ _ Bs Df S N h1 h2 w hw j
  have hμ : S.μ w = Bs.μ0 := by
    by_contra h
    exact hw ((h2 w).2 h)
  have hA : S.Aw j w = Atup S j Bs.μ0 w := by rw [← hμ]; rfl
  by_contra hc
  apply h1 w _ hμ
  refine ⟨j, ?_⟩
  by_cases hF : N.F0 w j = 0
  · left
    intro h0
    exact hc ⟨hA.trans h0, hF⟩
  · exact Or.inr hF

end Formalism.IndefR.NonGenericAndKTwoTheorems
