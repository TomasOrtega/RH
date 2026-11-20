import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

namespace GroundTheory.Automorphic

namespace AutomorphicForm

namespace CuspidalAutomorphicRepresentation

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Consider the cases of `π`. Consider the cases of `π'`. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
@[ext] theorem ext {π π' : CuspidalAutomorphicRepresentation K n} (h : π.carrier = π'.carrier) : π = π' := by
  cases π
  cases π'
  subst h
  rfl

/- English proof (translation)
Introduce `h`. Establish `hirr : IsSimpleOrder (Subrepresentation π.toModule.fullRep)` using `π.isIrreducible`. Apply `(bot_ne_top : (⊥ : Subrepresentation π.toModule.fullRep) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show (⊥ : Submodule ℂ π.carrier) = ⊤`.

Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Establish `hx : (x : cuspForms K n) ∈ (⊥ : Submodule ℂ (cuspForms K n))` using `h ▸ x.2`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Conclude with `Subtype.ext hx`.
-/
theorem carrier_ne_bot (π : CuspidalAutomorphicRepresentation K n) : π.carrier ≠ ⊥ := by
  intro h
  have hirr : IsSimpleOrder (Subrepresentation π.toModule.fullRep) := π.isIrreducible
  apply (bot_ne_top : (⊥ : Subrepresentation π.toModule.fullRep) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  show (⊥ : Submodule ℂ π.carrier) = ⊤
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (x : cuspForms K n) ∈ (⊥ : Submodule ℂ (cuspForms K n)) := h ▸ x.2
  rw [Submodule.mem_bot] at hx ⊢
  exact Subtype.ext hx

/- English proof (translation)
The claim follows from `Submodule.exists_mem_ne_zero_of_ne_bot π.carrier_ne_bot`.
-/
theorem exists_mem_ne_zero (π : CuspidalAutomorphicRepresentation K n) : ∃ φ ∈ π.carrier, φ ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot π.carrier_ne_bot

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end GroundTheory.Automorphic
