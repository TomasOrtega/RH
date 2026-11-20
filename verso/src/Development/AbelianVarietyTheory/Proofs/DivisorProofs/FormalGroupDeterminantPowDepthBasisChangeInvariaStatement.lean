import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetDepthBasis.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalGroupDeterminantPowDepthBasisChangeInvaria.lean&line=204#L204)
-/
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 → detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  first | exact @GlobalTheory.DetDepthBasis.main | exact GlobalTheory.DetDepthBasis.main | (intros; apply GlobalTheory.DetDepthBasis.main <;> assumption)
