import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenImmersionOfMonoOfSmoothOfRelativeDimension.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.isOpenImmersion_of_mono_of_smoothOfRelativeDimension' : ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  first | exact @GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | exact GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | (intros; apply GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension <;> assumption)
