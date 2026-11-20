import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.isRat_of_hankel_eventually_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRatOfHankelEventuallyZero.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.isRat_of_hankel_eventually_eq_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  first | exact @GlobalTheory.Nef.isRat_of_hankel_eventually_zero | exact GlobalTheory.Nef.isRat_of_hankel_eventually_zero | (intros; apply GlobalTheory.Nef.isRat_of_hankel_eventually_zero <;> assumption)
