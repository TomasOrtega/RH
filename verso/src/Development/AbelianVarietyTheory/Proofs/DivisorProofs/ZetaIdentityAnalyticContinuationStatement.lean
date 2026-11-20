import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIdentityAnalyticContinuation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GJReg.sum_chiS_eq_of_halfPlane` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FZetaIdentityAnalyticContinuation.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.zeta_identity_analytic_continuation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ν : kˣ →* ℂˣ) (m m' : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k) (c' : Fin m' → ℂ)
    (h' : Fin m' → GL (Fin n) k) (s₀ : ℝ),
    (∀ s : ℂ, s₀ < s.re → ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i)) →
    ∀ s : ℂ, ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i) := by
  first | exact @GlobalTheory.GJReg.sum_chiS_eq_of_halfPlane | exact GlobalTheory.GJReg.sum_chiS_eq_of_halfPlane | (intros; apply GlobalTheory.GJReg.sum_chiS_eq_of_halfPlane <;> assumption)
