import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtale
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FApproxPthRootFixedSubfieldOfAlmostEtale.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.FiniteIndex → AlmostSep v N → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ApproxRoot p v (Fix L N) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | exact GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep | (intros; apply GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep <;> assumption)
