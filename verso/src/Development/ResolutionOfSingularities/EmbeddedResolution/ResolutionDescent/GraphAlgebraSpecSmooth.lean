import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth

universe u

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]

/- English proof (translation)
Rewrite using `[HasRingHomProperty.Spec_iff (P := @Smooth)]`. Establish `: Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v)` using `isStandardSmooth_graphAlgebraAway f v hv`. Use `show @Algebra.Smooth _ _ _ _ (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra`. Establish `h : (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra = (inferInstance : Algebra (MvPolynomial τ R) (GraphAlgebraAway f v))` using `Algebra.algebra_ext _ _ fun _ => rfl`. Rewrite using `[h]`.

Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> infer_instance`.
-/
theorem smooth_specMap_algebraMap_graphAlgebraAway [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) :=
    isStandardSmooth_graphAlgebraAway f v hv
  show @Algebra.Smooth _ _ _ _ (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra
  have h : (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra =
      (inferInstance : Algebra (MvPolynomial τ R) (GraphAlgebraAway f v)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [h]
  refine ⟨?_, ?_⟩ <;> infer_instance

/- English proof (translation)
Establish `: IsLocalization.Away (graphJacobianMinorDet f v) (GraphAlgebraAway f v)` using `inferInstance`. Conclude with `IsOpenImmersion.of_isLocalization (graphJacobianMinorDet f v) ..`.
-/
theorem isOpenImmersion_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) := by
  have : IsLocalization.Away (graphJacobianMinorDet f v) (GraphAlgebraAway f v) := inferInstance
  exact IsOpenImmersion.of_isLocalization (graphJacobianMinorDet f v) ..

instance instIsOpenImmersionSpecMapGraphAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))) :=
  isOpenImmersion_specMap_algebraMap_graphAlgebraAway f v

/- English proof (translation)
Establish `h` using `PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)`. Conclude with `h`.
-/
theorem range_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) (graphJacobianMinorDet f v)
  exact h

/- English proof (translation)
The claim follows from `IsScalarTower.algebraMap_eq (MvPolynomial τ R) (GraphAlgebra f) (GraphAlgebraAway f v)`.
-/
theorem algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)) =
      (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)).comp
        (algebraMap (MvPolynomial τ R) (GraphAlgebra f)) :=
  IsScalarTower.algebraMap_eq (MvPolynomial τ R) (GraphAlgebra f) (GraphAlgebraAway f v)

/- English proof (translation)
Rewrite using `[algebraMap_graphAlgebraAway_eq_comp f v, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem specMap_algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v))) =
      Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebra f))) := by
  rw [algebraMap_graphAlgebraAway_eq_comp f v, CommRingCat.ofHom_comp, Spec.map_comp]

end FunctorialResolution.EmbeddedResolution
