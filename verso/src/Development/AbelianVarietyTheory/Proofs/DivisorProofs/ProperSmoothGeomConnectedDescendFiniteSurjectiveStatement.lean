import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProperSmoothGeomConnectedDescendFiniteSurjective.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f → GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  first | exact @GlobalTheory.DualCon.good_of_isPullback_finite_surjective | exact GlobalTheory.DualCon.good_of_isPullback_finite_surjective | (intros; apply GlobalTheory.DualCon.good_of_isPullback_finite_surjective <;> assumption)
