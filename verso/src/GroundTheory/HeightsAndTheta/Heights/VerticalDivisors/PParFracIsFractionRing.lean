import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Introduce `K _ _ e n v`. Set `` to `(parToFrac e n v).toAlgebra`. Establish `: IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n)` using `IsScalarTower.of_algebraMap_eq fun x => by`. Express the relevant statement in the definitionally equal form `_ = parToFrac e n v (algebraMap _ _ x)`. Unfold `parToFrac`.

Rewrite using `[IsLocalization.lift_eq]`. Conclude with `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl (ParDVR e n v) (ParFrac K e n)`.
-/
theorem ParFracIsFractionRing.proof : ParFracIsFractionRing.Statement := by
  intro K _ _ e n v
  let := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = parToFrac e n v (algebraMap _ _ x)
      unfold parToFrac
      rw [IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl
    (ParDVR e n v) (ParFrac K e n)

end

end GroundTheory.Heights₂.Heights.Vertical
