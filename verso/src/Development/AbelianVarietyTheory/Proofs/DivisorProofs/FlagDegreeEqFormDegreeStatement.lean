import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagDegreeEqFormDegree.lean&line=235#L235)
-/
theorem _root_.GlobalTheory.T.flag_degree_eq_form_degree : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : Pol ι N), degFl ι N P = formDeg (toForm P) := by
  first | exact @GlobalTheory.FlagFormDeg.degFl_eq_formDeg | exact GlobalTheory.FlagFormDeg.degFl_eq_formDeg | (intros; apply GlobalTheory.FlagFormDeg.degFl_eq_formDeg <;> assumption)
