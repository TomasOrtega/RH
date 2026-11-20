import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProof
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.BalancedPointPf.balancedPoint | exact GlobalTheory.BalancedPointPf.balancedPoint | (intros; apply GlobalTheory.BalancedPointPf.balancedPoint <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.existsBalancedFrameCMUnitary_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  first | exact @GlobalTheory.BalancedPointPf.balancedPoint | exact GlobalTheory.BalancedPointPf.balancedPoint | (intros; apply GlobalTheory.BalancedPointPf.balancedPoint <;> assumption)
