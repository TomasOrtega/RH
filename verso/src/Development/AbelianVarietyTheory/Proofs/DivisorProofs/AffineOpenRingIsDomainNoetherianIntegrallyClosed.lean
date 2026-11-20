import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hne : Nonempty (U : X.Opens)`. Take `⟨x, hx⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hU0`. Conclude with `⟨⟨x, hx⟩⟩`. Use `haveI : IsDomain Γ(X, U) := IsIntegral.component_integral (U : X.Opens)`. Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U`.

Use `⟨inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Establish `hUa : IsAffineOpen (U : X.Opens)` using `U.2`. Use `IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_` and prove the remaining obligations. Establish `hy : hUa.fromSpec ⟨p, hp.isPrime⟩ ∈ (U : X.Opens)` using `hUa.range_fromSpec.le ⟨_, rfl⟩`. Use `letI := X.presheaf.algebra_section_stalk ⟨_, hy⟩`.

Establish `hl` using `hUa.isLocalization_stalk' ⟨p, hp.isPrime⟩ hy`. Use `haveI := (hN (hUa.fromSpec ⟨p, hp.isPrime⟩)).2`. Conclude with `IsIntegrallyClosed.of_equiv (@IsLocalization.algEquiv _ _ p.primeCompl _ _ (X.presheaf.algebra_section_stalk ⟨_, hy⟩) hl (Localization.AtPrime p) _ _ _).toRingEquiv`.
-/
theorem affineOpen_ring_isDomain_noetherian_integrallyClosed (X : Scheme.{0}) (hX : IsIntegral X)
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X) (U : X.affineOpens)
    (hU0 : (U : X.Opens) ≠ ⊥) :
    IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) := by
  have hne : Nonempty (U : X.Opens) := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hU0
    exact ⟨⟨x, hx⟩⟩
  haveI : IsDomain Γ(X, U) := IsIntegral.component_integral (U : X.Opens)
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hUa : IsAffineOpen (U : X.Opens) := U.2
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  have hy : hUa.fromSpec ⟨p, hp.isPrime⟩ ∈ (U : X.Opens) := hUa.range_fromSpec.le ⟨_, rfl⟩
  letI := X.presheaf.algebra_section_stalk ⟨_, hy⟩
  have hl := hUa.isLocalization_stalk' ⟨p, hp.isPrime⟩ hy
  haveI := (hN (hUa.fromSpec ⟨p, hp.isPrime⟩)).2
  exact IsIntegrallyClosed.of_equiv
    (@IsLocalization.algEquiv _ _ p.primeCompl _ _
      (X.presheaf.algebra_section_stalk ⟨_, hy⟩) hl (Localization.AtPrime p) _ _ _).toRingEquiv

end GlobalTheory
