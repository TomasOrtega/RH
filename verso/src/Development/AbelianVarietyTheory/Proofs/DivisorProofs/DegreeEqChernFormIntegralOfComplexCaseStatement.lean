import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDegreeEqChernFormIntegralOfComplexCase.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
