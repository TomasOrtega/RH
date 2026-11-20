import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebraStandardSmooth

universe u

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]

/- English proof (authored)
The graph algebra localized at the chosen Jacobian minor is standard smooth over the ring of the graph coordinates. Its algebra map is therefore smooth. The affine correspondence between smooth ring maps and smooth morphisms of spectra gives the claim.
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

/- English proof (authored)
The localized graph algebra is obtained by inverting the chosen Jacobian minor. The map on spectra of a localization at one element is the inclusion of the corresponding basic open.
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

/- English proof (authored)
Prime ideals of the localized graph algebra correspond by contraction to prime ideals of the original graph algebra that avoid the powers of the Jacobian minor. These are precisely the points of the basic open of the minor.
-/
theorem range_specMap_algebraMap_graphAlgebraAway
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) (graphJacobianMinorDet f v)
  exact h

/- English proof (authored)
The ring of graph coordinates acts on the localization through its map to the graph algebra and the localization map. This is the composite of the two algebra maps in the scalar tower.
-/
theorem algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)) =
      (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)).comp
        (algebraMap (MvPolynomial τ R) (GraphAlgebra f)) :=
  IsScalarTower.algebraMap_eq (MvPolynomial τ R) (GraphAlgebra f) (GraphAlgebraAway f v)

/- English proof (authored)
Factor the algebra map through the graph algebra by the scalar tower. Taking spectra reverses the order of the two factors, giving the stated composite of scheme maps.
-/
theorem specMap_algebraMap_graphAlgebraAway_eq_comp
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v))) =
      Spec.map (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebra f))) := by
  rw [algebraMap_graphAlgebraAway_eq_comp f v, CommRingCat.ofHom_comp, Spec.map_comp]

end FunctorialResolution.EmbeddedResolution
