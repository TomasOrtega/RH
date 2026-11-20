import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

variable (E : Type*) [Field E] [NumberField E]
variable (W : Type*) [AddCommGroup W] [Module E W]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem LineIndexCoeffs.proof : LineIndexCoeffs.Statement (E := E) W := by
  intro La x hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hfa : ∀ a : E, f a = a • x := fun a => rfl
  have hf : Function.Injective f := by
    intro a b hab
    rw [hfa, hfa] at hab
    exact smul_left_injective E hx hab
  have h1 : (intSubgroup E).map f = ringMultiples E x := by
    rw [intSubgroup, ringMultiples, AddMonoidHom.range_comp]
  have hrange : f.range = (Submodule.span E {x}).toAddSubgroup := by
    ext y
    simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
      hfa]
  have h2 : (lineCoeffs La x).map f = La ⊓ (Submodule.span E {x}).toAddSubgroup := by
    rw [lineCoeffs, AddSubgroup.map_comap_eq, hrange, inf_comm]
  unfold lineIndex
  rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end GroundTheory.Heights₂.Heights.FiniteCovolume
