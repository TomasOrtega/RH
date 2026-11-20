import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

/- English proof (translation)
Use `haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) := reflectsColimitsOfShape_of_reflectsIsomorphisms`. Use `⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩` and prove the remaining obligations. Use `Types.FilteredColimit.isColimitOf _ _ ?_ ?_` and prove the remaining obligations. Introduce `x`. Express the relevant statement in the definitionally equal form `Ω at x`.

Establish `hx : _root_.IsIntegral K x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Use `haveI := IntermediateField.adjoin.finiteDimensional hx`. Conclude with `⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩, ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩`. Introduce `i j xi xj h`. Use `⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩, homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h`.
-/
theorem ringCocone_isColimit (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] :
    Nonempty (IsColimit (ringCocone K Ω)) := by
  haveI : ReflectsColimitsOfShape (FinSub K Ω) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change Ω at x
    have hx : _root_.IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    haveI := IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, inferInstance⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, by haveI := i.2; haveI := j.2; infer_instance⟩,
      homOfLE (le_sup_left (a := i.1)), homOfLE (le_sup_right (b := j.1)), ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.SepCech
