import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLocallyNoetherianOfSmoothOverModification.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  first | exact @GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | exact GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | (intros; apply GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif <;> assumption)
