import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrder
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.moves_top_of_coprime_order` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FMovesIntegersAlmostUnitOfCoprimeOrder.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 → (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_top_of_coprime_order | exact GlobalTheory.AlmostEt.moves_top_of_coprime_order | (intros; apply GlobalTheory.AlmostEt.moves_top_of_coprime_order <;> assumption)
