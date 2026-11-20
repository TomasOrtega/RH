import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquares
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.galEqN_of_squares` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionLabelsGaloisAllLevelsOfSquares.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.torsionLabels_galois_all_levels_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  first | exact @GlobalTheory.Mum.galEqN_of_squares | exact GlobalTheory.Mum.galEqN_of_squares | (intros; apply GlobalTheory.Mum.galEqN_of_squares <;> assumption)
