import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Introduce `k L _ _ _ C X c u x hpb`. Establish `hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L)))`. Rewrite using `[surjective_iff]`. Introduce `p`. Take `⟨q⟩ : Nonempty (Spec (CommRingCat.of L))` from `inferInstanceAs (Nonempty (PrimeSpectrum L))`.

Use `⟨q, ?_⟩` and prove the remaining obligations. Conclude with `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Conclude with `MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hs`.
-/
theorem UpperTheory.surjective_of_isPullback_spec_field_ext :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → Surjective u := by
  intro k L _ _ _ C X c u x hpb
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [surjective_iff]
    intro p
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine ⟨q, ?_⟩
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hs
