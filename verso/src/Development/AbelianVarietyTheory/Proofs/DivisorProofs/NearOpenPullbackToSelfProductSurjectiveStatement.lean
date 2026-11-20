import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenPullbackToSelfProductSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNearOpenPullbackToSelfProductSurjective.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.nearOpenPullbackToSelfProduct_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  first | exact @GlobalTheory.Mum.Desc.surjective_UT_hom | exact GlobalTheory.Mum.Desc.surjective_UT_hom | (intros; apply GlobalTheory.Mum.Desc.surjective_UT_hom <;> assumption)
