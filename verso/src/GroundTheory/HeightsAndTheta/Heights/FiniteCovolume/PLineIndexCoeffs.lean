import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

variable (E : Type*) [Field E] [NumberField E]
variable (W : Type*) [AddCommGroup W] [Module E W]

/- English proof (translation)
Introduce `La x hx`. Set `f : E →+ W` to `(smulAddHom E W).flip x`. Establish `hfa : ∀ a : E, f a = a • x` using `fun a => rfl`. Establish `hf : Function.Injective f`. Introduce `a b hab`.

Rewrite `hab` using `[hfa, hfa]`. Conclude with `smul_left_injective E hx hab`. Establish `h1 : (intSubgroup E).map f = ringMultiples E x`. Rewrite using `[intSubgroup, ringMultiples, AddMonoidHom.range_comp]`. Establish `hrange : f.range = (Submodule.span E {x}).toAddSubgroup`.

Use extensionality with `y`. Simplify using `only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, hfa]`. Establish `h2 : (lineCoeffs La x).map f = La ⊓ (Submodule.span E {x}).toAddSubgroup`. Rewrite using `[lineCoeffs, AddSubgroup.map_comap_eq, hrange, inf_comm]`. Unfold `lineIndex`.

Rewrite using `[← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf]`.
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
