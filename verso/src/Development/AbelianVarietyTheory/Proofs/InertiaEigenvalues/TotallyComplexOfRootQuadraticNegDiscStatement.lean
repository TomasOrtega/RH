import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexOfRootQuadraticNegDisc
import Mathlib
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTotallyComplexOfRootQuadraticNegDisc.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isTotallyComplex_of_root_quadratic_neg_disc : ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  first | exact @GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | exact GlobalTheory.totallyComplex_of_root_quadratic_neg_disc | (intros; apply GlobalTheory.totallyComplex_of_root_quadratic_neg_disc <;> assumption)
