import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem expOf_twoSided_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧
      ∀ ex, IsExp G ex → ex = expOf G := by
  intro C _ _ v d G
  obtain ⟨h1, h2, h3⟩ := expOf_spec G
  exact ⟨h1, h3, h2⟩

end GlobalTheory.FGDepth
