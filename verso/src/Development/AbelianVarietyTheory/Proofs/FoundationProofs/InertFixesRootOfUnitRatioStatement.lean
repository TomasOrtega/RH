import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.inert_fixes_root_of_unit_ratio` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FInertFixesRootOfUnitRatio.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω),
  0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N → B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  first | exact @GlobalTheory.inert_fixes_root_of_unit_ratio | exact GlobalTheory.inert_fixes_root_of_unit_ratio | (intros; apply GlobalTheory.inert_fixes_root_of_unit_ratio <;> assumption)
