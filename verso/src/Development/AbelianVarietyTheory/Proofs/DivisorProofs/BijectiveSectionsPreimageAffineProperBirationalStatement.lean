import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZariskiSections.bijective_appTop_restrict` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBijectiveSectionsPreimageAffineProperBirational.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.bijective_sections_preimage_affine_proper_birational : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V → Function.Bijective (π ∣_ V).appTop := by
  first | exact @GlobalTheory.ZariskiSections.bijective_appTop_restrict | exact GlobalTheory.ZariskiSections.bijective_appTop_restrict | (intros; apply GlobalTheory.ZariskiSections.bijective_appTop_restrict <;> assumption)
