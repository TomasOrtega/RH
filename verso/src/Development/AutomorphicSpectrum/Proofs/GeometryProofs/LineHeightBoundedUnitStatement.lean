import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnit
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLineHeightBoundedUnit.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.line_height_bounded_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit <;> assumption)
