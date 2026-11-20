import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeMulNFiniteFlatSurjective.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 0 < n → IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  first | exact @GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | exact GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN | (intros; apply GlobalTheory.MulFlatSurj.finite_flat_surjective_mulN <;> assumption)
