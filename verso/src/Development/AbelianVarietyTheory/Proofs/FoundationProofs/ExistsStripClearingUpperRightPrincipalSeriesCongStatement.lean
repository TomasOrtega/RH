import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsStripClearingUpperRightPrincipalSeriesCong
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsStripClearingUpperRightPrincipalSeriesCong.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0, ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  first | exact @GlobalTheory.PsType.clear_upper_right | exact GlobalTheory.PsType.clear_upper_right | (intros; apply GlobalTheory.PsType.clear_upper_right <;> assumption)
