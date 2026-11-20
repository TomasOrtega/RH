import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ r h x`. Establish `hs : Algebra.Smooth R (MvPolynomial (Fin r) R)` using `⟨inferInstance, inferInstance⟩`. Set `f : Sp (MvPolynomial (Fin r) R) ⟶ Sp R` to `Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin r) R)))`. Establish `: Smooth f`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Smooth)]`.

Conclude with `RingHom.smooth_algebraMap.mpr hs`. Conclude with `forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f h x`.
-/
theorem isNormalScheme_sp_mvPolynomial :
    ∀ (R : Type) [CommRing R] (r : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial (Fin r) R)) := by
  intro R _ r h x
  have hs : Algebra.Smooth R (MvPolynomial (Fin r) R) := ⟨inferInstance, inferInstance⟩
  let f : Sp (MvPolynomial (Fin r) R) ⟶ Sp R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin r) R)))
  have : Smooth f := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hs
  exact forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f h x

end GlobalTheory
