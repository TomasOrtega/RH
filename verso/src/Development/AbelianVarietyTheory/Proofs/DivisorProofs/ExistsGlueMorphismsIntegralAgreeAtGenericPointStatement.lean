import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.GenGlue.exists_glue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGlueMorphismsIntegralAgreeAtGenericPoint.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) → ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P), (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) → ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  first | exact @GlobalTheory.Desc.GenGlue.exists_glue | exact GlobalTheory.Desc.GenGlue.exists_glue | (intros; apply GlobalTheory.Desc.GenGlue.exists_glue <;> assumption)
