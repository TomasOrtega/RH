import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntBall.Cutoff.ofReal_bnd_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOfRealGramDeterminantBoundLeProdCutoff.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  first | exact @GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | exact GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | (intros; apply GlobalTheory.IntBall.Cutoff.ofReal_bnd_le <;> assumption)
