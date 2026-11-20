import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

namespace GroundTheory.Automorphic

namespace AutomorphicForm

namespace CuspidalAutomorphicRepresentation

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Substitute using the available equality. Both sides reduce to the same expression.
-/
@[ext] theorem ext {π π' : CuspidalAutomorphicRepresentation K n} (h : π.carrier = π'.carrier) : π = π' := by
  cases π
  cases π'
  subst h
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem exists_mem_ne_zero (π : CuspidalAutomorphicRepresentation K n) : ∃ φ ∈ π.carrier, φ ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot π.carrier_ne_bot

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end GroundTheory.Automorphic
