import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBounds
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAmpleHeightBounds.lean&line=370#L370)
-/
theorem _root_.GlobalTheory.T.ample_height_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | exact GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound <;> assumption)
