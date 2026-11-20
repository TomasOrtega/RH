import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement

namespace Formalism.IndefR.NonGenericAndKTwoTheorems

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef Formalism.IndefR.HeckeTupleConditions

/- English proof (translation)
Introduce `K _ _ _ Bs Df S N h1 h2 w hw j`. Establish `hμ : S.μ w = Bs.μ0`. Assume the negation of the conclusion as `h`. Conclude with `hw ((h2 w).2 h)`. Establish `hA : S.Aw j w = Atup S j Bs.μ0 w` using `by rw [← hμ]; rfl`.

Assume the negation of the conclusion as `hc`. Apply `h1 w _ hμ` to reduce the goal to its premises. Use `⟨j, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hF : N.F0 w j = 0`. Use `left`.

Introduce `h0`. Conclude with `hc ⟨hA.trans h0, hF⟩`. Conclude with `Or.inr hF`.
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
