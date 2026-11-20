import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Published.arShift_of_arChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithSelfInterConstantShiftOfTrivialWeightFormul.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  first | exact @GlobalTheory.Published.arShift_of_arChange | exact GlobalTheory.Published.arShift_of_arChange | (intros; apply GlobalTheory.Published.arShift_of_arChange <;> assumption)
