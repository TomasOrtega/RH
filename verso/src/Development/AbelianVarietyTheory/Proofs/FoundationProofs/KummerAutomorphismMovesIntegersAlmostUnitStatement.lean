import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerAutomorphismMovesIntegersAlmostUnit.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) → ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.kummer_moves | exact GlobalTheory.AlmostEt.kummer_moves | (intros; apply GlobalTheory.AlmostEt.kummer_moves <;> assumption)
