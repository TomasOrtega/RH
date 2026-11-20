import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSmallPointsCoordRatioBound.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.small_points_coord_ratio_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | exact GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms <;> assumption)
