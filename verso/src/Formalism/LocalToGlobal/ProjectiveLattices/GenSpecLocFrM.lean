import Mathlib

noncomputable section

namespace Formalism.L2.Pj.LocFrM

open TensorProduct

variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

/- English proof (translation)
Use `Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨x, y, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show e (e y) = e y`.

Conclude with `LinearMap.congr_fun he y`.
-/
theorem range_projective (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show e (e y) = e y
  exact LinearMap.congr_fun he y

/- English proof (translation)
Use `haveI := range_projective e he`. Use `haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
theorem range_free (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by
  haveI := range_projective e he
  haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

section Split

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

end Formalism.L2.Pj.LocFrM
