import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RebasedTypicalCurvesIsBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRebasedTypicalCurvesIsBasis.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.rebased_typical_curves_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  first | exact @GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis | exact GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis | (intros; apply GlobalTheory.DepthStages.RebaseBasis.rebase_isBasis <;> assumption)
