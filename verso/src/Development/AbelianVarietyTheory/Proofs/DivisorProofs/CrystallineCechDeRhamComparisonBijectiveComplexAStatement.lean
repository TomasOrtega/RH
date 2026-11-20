import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCrystallineCechDeRhamComparisonBijectiveComplexA.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  first | exact @GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | exact GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | (intros; apply GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian <;> assumption)
