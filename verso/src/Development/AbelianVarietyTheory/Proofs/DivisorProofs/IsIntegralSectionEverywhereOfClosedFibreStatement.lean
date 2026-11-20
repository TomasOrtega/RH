import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.intAt_of_closedFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIntegralSectionEverywhereOfClosedFibre.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), (∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x) → ∀ x : G.left, IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_closedFibre | exact GlobalTheory.Mum.intAt_of_closedFibre | (intros; apply GlobalTheory.Mum.intAt_of_closedFibre <;> assumption)
