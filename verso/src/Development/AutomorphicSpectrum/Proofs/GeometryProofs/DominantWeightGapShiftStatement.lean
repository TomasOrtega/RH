import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShift
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FDominantWeightGapShift.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.dominant_weight_gap_shift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N → 0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) → CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧ ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | exact GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant <;> assumption)
