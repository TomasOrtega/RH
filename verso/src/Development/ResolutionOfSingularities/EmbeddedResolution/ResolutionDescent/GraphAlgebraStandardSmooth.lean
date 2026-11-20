import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphAlgebra

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

noncomputable section

abbrev graphJacobianMinorDet [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det

abbrev GraphAlgebraAway [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) : Type u :=
  Localization.Away (graphJacobianMinorDet f v)

/- English proof (authored)
The algebra is localized at the powers of the minor determinant. The determinant itself belongs to those powers, so its image is a unit.
-/
theorem isUnit_algebraMap_graphJacobianMinorDet [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)) :=
  IsLocalization.map_units (M := Submonoid.powers (graphJacobianMinorDet f v)) (GraphAlgebraAway f v)
    ⟨graphJacobianMinorDet f v, Submonoid.mem_powers _⟩

/- English proof (authored)
The Jacobian of the graph presentation is the chosen minor determinant multiplied by a power of minus one. Both factors become units in the localization, so the image of their product is a unit.
-/
theorem isUnit_algebraMap_jacobian_graphPreSubmersive [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)
      (graphPreSubmersivePresentation f v hv).jacobian) := by
  rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
  exact ((isUnit_one.neg).pow _).mul (isUnit_algebraMap_graphJacobianMinorDet f v)

private def graphAlgebraAwayLocalizationPresentation [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Algebra.SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)

private def graphAlgebraAwayPreSubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v) (Unit ⊕ σ) (Unit ⊕ τ) :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)

/- English proof (authored)
The Jacobian of the composite presentation is the product of the image of the graph presentation's Jacobian and the Jacobian of the localization presentation. The first is a unit after localization, and the second is a unit because the localization presentation is submersive.
-/
private theorem isUnit_jacobian_presentation_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (isUnit_algebraMap_jacobian_graphPreSubmersive f v hv).mul (graphAlgebraAwayLocalizationPresentation f v).jacobian_isUnit

private def graphAlgebraAwaySubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.SubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (Fintype.card σ)) (Unit ⊕ Fin (Fintype.card τ)) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway f v hv }
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin σ).symm)
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin τ).symm)

/- English proof (authored)
Compose the graph presentation with the presentation adjoining the inverse of the minor determinant. The composite Jacobian is a unit by the product calculation, so this is a submersive presentation. Its sets of variables and relations are finite and can be reindexed by finite sets of the stated sizes. This presentation exhibits the algebra as standard smooth.
-/
theorem isStandardSmooth_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) := by
  constructor
  exact ⟨Unit ⊕ Fin (Fintype.card σ), Unit ⊕ Fin (Fintype.card τ), inferInstance, inferInstance,
    ⟨graphAlgebraAwaySubmersivePresentation f v hv⟩⟩

end

end FunctorialResolution.EmbeddedResolution
