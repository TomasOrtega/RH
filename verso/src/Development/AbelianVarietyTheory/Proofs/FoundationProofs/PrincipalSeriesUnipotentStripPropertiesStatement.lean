import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsType.strip_props` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPrincipalSeriesUnipotentStripProperties.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.principalSeriesUnipotentStrip_properties : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_props | exact GlobalTheory.PsType.strip_props | (intros; apply GlobalTheory.PsType.strip_props <;> assumption)
