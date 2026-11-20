import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAbelianSchemeOfGrpPullback.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isAbelianScheme_of_grpPullback' : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' := by
  first | exact @GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | exact GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback | (intros; apply GlobalTheory.GrpPullAb.isAbelianScheme_of_grpPullback <;> assumption)
