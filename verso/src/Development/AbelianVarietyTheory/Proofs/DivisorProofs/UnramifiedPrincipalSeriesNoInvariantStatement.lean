import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnramifiedPrincipalSeriesNoInvariant.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.unramified_principal_series_no_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 := by
  first | exact @GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed | exact GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed | (intros; apply GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed <;> assumption)
