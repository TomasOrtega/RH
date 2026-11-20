import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPr
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarishChandraSeriesWeightNonnegOfIdempotentGlnPr.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | exact GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime <;> assumption)
