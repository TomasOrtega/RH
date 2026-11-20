import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.isAbelianScheme_generic_of_injective` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAbelianSchemeGenericFibreInjectiveDomainMap.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  first | exact @GlobalTheory.Desc.isAbelianScheme_generic_of_injective | exact GlobalTheory.Desc.isAbelianScheme_generic_of_injective | (intros; apply GlobalTheory.Desc.isAbelianScheme_generic_of_injective <;> assumption)
