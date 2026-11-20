import Mathlib
import Formalism.PeriodIntegrals.JetsPhW

universe u_1

namespace Bl.FirstLemmaF

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries.{u_1, 0} σ (PadicComplex p)},
  PI.JetsPhW.IntegralMv.{u_1} F →
    PI.JetsPhW.IntegralMv.{u_1} G → PI.JetsPhW.IntegralMv.{u_1} (HMul.hMul.{u_1, u_1, u_1} F G) := by
  intro p _ σ F G hF hG n
  classical
  unfold PI.JetsPhW.IsIntP
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x : PadicComplex p => ‖x‖ ≤ 1) ?_ ?_ ?_
  · intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  · simp
  · intro x _
    rw [norm_mul]
    exact mul_le_one₀ (hF x.1) (norm_nonneg _) (hG x.2)

end Bl.FirstLemmaF
