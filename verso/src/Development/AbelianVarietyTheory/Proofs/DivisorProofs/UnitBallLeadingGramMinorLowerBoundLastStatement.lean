import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLast
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitBallLeadingGramMinorLowerBoundLast.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | exact GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | (intros; apply GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin <;> assumption)
