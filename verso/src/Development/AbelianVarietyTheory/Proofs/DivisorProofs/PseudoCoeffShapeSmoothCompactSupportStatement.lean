import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShapeSmoothFinite.stShape` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPseudoCoeffShapeSmoothCompactSupport.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport : GlobalTheory.PsCo.Pc1.StShape := by
  first | exact @GlobalTheory.ShapeSmoothFinite.stShape | exact GlobalTheory.ShapeSmoothFinite.stShape | (intros; apply GlobalTheory.ShapeSmoothFinite.stShape <;> assumption)
