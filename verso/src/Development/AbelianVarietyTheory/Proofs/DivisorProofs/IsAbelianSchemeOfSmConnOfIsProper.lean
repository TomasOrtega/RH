import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmConnProper

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, hp, h.2.2.2.2⟩`.
-/
theorem isAbelianScheme_of_smConn_of_isProper (S : Scheme.{0}) (G : Over S) [GrpObj G]
    (h : GlobalTheory.SS.SmConn G) (hp : IsProper G.hom) : IsAbelianScheme G :=
  ⟨h.1, h.2.1, hp, h.2.2.2.2⟩

/- English proof (translation)
Introduce `S G _ h hp` and use `isAbelianScheme_of_smConn_of_isProper S G h hp`.
-/
theorem main : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G :=
  fun S G _ h hp => isAbelianScheme_of_smConn_of_isProper S G h hp

end GlobalTheory.SmConnProper
