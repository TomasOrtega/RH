import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundleTrivialOnFibre.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.line_bundle_trivial_on_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  first | exact @GlobalTheory.KTrivJacobson.kTriv_of_quotient | exact GlobalTheory.KTrivJacobson.kTriv_of_quotient | (intros; apply GlobalTheory.KTrivJacobson.kTriv_of_quotient <;> assumption)
