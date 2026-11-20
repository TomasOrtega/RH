import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeAndArithmeticCompatibility
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TiesOnObj.ties_onObj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDegreeAndArithmeticCompatibility.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.degree_and_arithmetic_compatibility : Hypotheses2 → HypothesesH → OnObj fun _ _ A T _ _ => TieDeg T ∧ TieM T A ∧ TieAr A := by
  first | exact @GlobalTheory.TiesOnObj.ties_onObj | exact GlobalTheory.TiesOnObj.ties_onObj | (intros; apply GlobalTheory.TiesOnObj.ties_onObj <;> assumption)
