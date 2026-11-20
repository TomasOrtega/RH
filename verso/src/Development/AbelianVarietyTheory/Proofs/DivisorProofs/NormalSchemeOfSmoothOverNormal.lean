import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SmoothNormal

/- English proof (translation)
Introduce `B Y _ π n _ hB`. Establish `: Smooth π` using `SmoothOfRelativeDimension.smooth n π`. Conclude with `GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth π hB`.
-/
theorem isNormalScheme_of_smoothOfRelativeDimension :
    ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro B Y _ π n _ hB
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth π hB

end GlobalTheory.SmoothNormal
