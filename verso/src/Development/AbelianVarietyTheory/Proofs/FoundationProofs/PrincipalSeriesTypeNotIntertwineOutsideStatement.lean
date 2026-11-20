import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeNotIntertwineOutside
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesTypeNotIntertwineOutside.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.principalSeriesType_not_intertwine_outside : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ y ∈ KO k (Fin n), y ∉ grp ψ → ∃ j ∈ grp ψ, y * j * y⁻¹ ∈ grp ψ ∧ theta ψ j ≠ theta ψ (y * j * y⁻¹) := by
  first | exact @GlobalTheory.PsType.not_intertwine | exact GlobalTheory.PsType.not_intertwine | (intros; apply GlobalTheory.PsType.not_intertwine <;> assumption)
