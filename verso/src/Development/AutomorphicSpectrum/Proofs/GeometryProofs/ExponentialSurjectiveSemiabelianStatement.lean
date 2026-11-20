import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExponentialFamilyPeriods
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExponentialSurjectiveSemiabelian.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exponential_surjective_semiabelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective <;> assumption)
