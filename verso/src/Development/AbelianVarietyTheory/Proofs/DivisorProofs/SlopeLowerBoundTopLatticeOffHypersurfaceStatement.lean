import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSShort.SlopeTop.slopeBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSlopeLowerBoundTopLatticeOffHypersurface.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface : SlopeBound := by
  first | exact @GlobalTheory.HSShort.SlopeTop.slopeBound | exact GlobalTheory.HSShort.SlopeTop.slopeBound | (intros; apply GlobalTheory.HSShort.SlopeTop.slopeBound <;> assumption)
