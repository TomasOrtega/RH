import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

noncomputable section

variable {E : Type*} [Field E]
variable (W : Type*) [AddCommGroup W] [Module E W]

/- English proof (translation)
Introduce `La x hLa hx`. Set `f : E →+ W` to `(smulAddHom E W).flip x`. Establish `hf : Function.Injective f.toIntLinearMap`. Introduce `a b hab`. Establish `h : a • x = b • x` using `hab`.

Conclude with `smul_left_injective E hx h`. Establish `hS : La.toIntSubmodule.FG`. Rewrite using `[Submodule.fg_iff_addSubgroup_fg]`. Simplify using `using hLa`. Establish `hle : (lineCoeffs (E` using `E) La x).toIntSubmodule.map f.toIntLinearMap ≤ La.toIntSubmodule := by`.

Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `ha`. Establish `hN : (lineCoeffs (E` using `E) La x).toIntSubmodule.FG := Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)`. Rewrite `hN` using `[Submodule.fg_iff_addSubgroup_fg]`. Simplify using `using hN`.
-/
theorem LineCoeffsFG.proof : LineCoeffsFG.Statement (E := E) W := by
  intro La x hLa hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hf : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have h : a • x = b • x := hab
    exact smul_left_injective E hx h
  have hS : La.toIntSubmodule.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]
    simpa using hLa
  have hle : (lineCoeffs (E := E) La x).toIntSubmodule.map f.toIntLinearMap ≤
      La.toIntSubmodule := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hN : (lineCoeffs (E := E) La x).toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)
  rw [Submodule.fg_iff_addSubgroup_fg] at hN
  simpa using hN

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
