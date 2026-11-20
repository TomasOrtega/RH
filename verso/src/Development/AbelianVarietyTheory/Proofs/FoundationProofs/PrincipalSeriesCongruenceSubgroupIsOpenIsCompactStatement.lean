import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.grp_isOpen_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesCongruenceSubgroupIsOpenIsCompact.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_isOpen_isCompact | exact GlobalTheory.PsType.grp_isOpen_isCompact | (intros; apply GlobalTheory.PsType.grp_isOpen_isCompact <;> assumption)
