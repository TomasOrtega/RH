import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FNumberFieldPointHeight.lean&line=414#L414)
-/
theorem _root_.GlobalTheory.T.number_field_point_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L P, IsArithVar (mCoordIdeal w) 1 ∧ P ≤ mCoordIdeal w ∧ (∀ f : MRing ι, (∃ a, IsMultiHomog f a) → (f ∈ mCoordIdeal w ↔ aeval w f = 0)) ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι (mCoordIdeal w) 1 ![A] / (degC (mCoordIdeal w) : ℝ) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | exact GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height <;> assumption)
