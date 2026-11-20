import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAlmostPurityOfNormalFiniteIndexSubgroup.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex → (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | exact GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex | (intros; apply GlobalTheory.AlmostEt.almostSep_of_normal_finiteIndex <;> assumption)
