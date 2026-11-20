import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
/- English proof (citation)
Apply `GlobalTheory.zelevinskyPolynomialRing_of_parts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FZelevinskyGrothendieckPolynomialRingOfSegments.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.zelevinskyGrothendieckPolynomialRing_of_segments : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation → GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  first | exact @GlobalTheory.zelevinskyPolynomialRing_of_parts | exact GlobalTheory.zelevinskyPolynomialRing_of_parts | (intros; apply GlobalTheory.zelevinskyPolynomialRing_of_parts <;> assumption)
