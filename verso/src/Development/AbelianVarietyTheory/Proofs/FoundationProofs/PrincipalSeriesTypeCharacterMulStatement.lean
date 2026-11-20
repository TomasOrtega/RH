import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterMul
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.theta_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesTypeCharacterMul.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, theta ψ (a * b) = theta ψ a * theta ψ b := by
  first | exact @GlobalTheory.PsType.theta_mul | exact GlobalTheory.PsType.theta_mul | (intros; apply GlobalTheory.PsType.theta_mul <;> assumption)
