import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAbelianSchemeNsmulSurjective.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.abelianScheme_nsmul_surjective : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | exact GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme <;> assumption)
