import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarmonicPolynomialLattices.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.small_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.SmallSt := by
  first | exact @GlobalTheory.SmallSpan.smallSt | exact GlobalTheory.SmallSpan.smallSt | (intros; apply GlobalTheory.SmallSpan.smallSt <;> assumption)
