import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScaling
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLineHeightInvariantScaling.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.line_height_invariant_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale <;> assumption)
