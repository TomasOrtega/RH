import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientData
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMaximalCompactPseudoCoefficientData.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  first | exact @GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | exact GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' | (intros; apply GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData' <;> assumption)
