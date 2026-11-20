import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FStripsExhaustParabolicUnipotentRadical.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_exhaust | exact GlobalTheory.PsType.strip_exhaust | (intros; apply GlobalTheory.PsType.strip_exhaust <;> assumption)
