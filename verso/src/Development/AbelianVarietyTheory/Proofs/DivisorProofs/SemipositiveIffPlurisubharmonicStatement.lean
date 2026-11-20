import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveIffPlurisubharmonic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemipositiveIffPlurisubharmonic.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.semipositive_iff_plurisubharmonic : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → Dominant O.Y (A.sh u s) → (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) → (O.Y.semipos (O.Y.Mbar B u s) ↔ ∀ c σ, IsPsh ((T.M c).A σ) ((T.F c).form (A.sh u s) s ((T.F c).phS (A.sh u s) s) σ)) := by
  first | exact @GlobalTheory.SemiposObj.semipos_onObj | exact GlobalTheory.SemiposObj.semipos_onObj | (intros; apply GlobalTheory.SemiposObj.semipos_onObj <;> assumption)
