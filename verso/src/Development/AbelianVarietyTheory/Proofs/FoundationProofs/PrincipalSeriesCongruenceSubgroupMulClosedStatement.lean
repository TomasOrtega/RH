import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.grp_mul_closed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesCongruenceSubgroupMulClosed.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ := by
  first | exact @GlobalTheory.PsType.grp_mul_closed | exact GlobalTheory.PsType.grp_mul_closed | (intros; apply GlobalTheory.PsType.grp_mul_closed <;> assumption)
