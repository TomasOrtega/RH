import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyAndPolynomialsExist
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mean4O.exists_limFam_and_tiePs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLimitFamilyAndPolynomialsExist.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.limit_family_and_polynomials_exist : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y), (∀ c, (T.F c).FamR Y.j) → (TieDeg T → ∃ Φ, LimFam (Y := Y) Φ) ∧ ∀ A : SlopeTestRemainingChoices Y, ∃ Ps, TiePs T { A with Ps := Ps } := by
  first | exact @GlobalTheory.Mean4O.exists_limFam_and_tiePs | exact GlobalTheory.Mean4O.exists_limFam_and_tiePs | (intros; apply GlobalTheory.Mean4O.exists_limFam_and_tiePs <;> assumption)
