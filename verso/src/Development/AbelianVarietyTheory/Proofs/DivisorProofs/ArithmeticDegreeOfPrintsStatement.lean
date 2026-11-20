import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticDegreeOfHyp.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.arithmetic_degree_of_known_theorems : Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => TieAr A := by
  first | exact @GlobalTheory.Mean4O.TieArObj.tieAr_onObj | exact GlobalTheory.Mean4O.TieArObj.tieAr_onObj | (intros; apply GlobalTheory.Mean4O.TieArObj.tieAr_onObj <;> assumption)
