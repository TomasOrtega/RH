import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatCrit.isRat_of_adelic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsRationalPowerSeriesOfAdelicIntegralPositiveRad.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  first | exact @GlobalTheory.RatCrit.isRat_of_adelic | exact GlobalTheory.RatCrit.isRat_of_adelic | (intros; apply GlobalTheory.RatCrit.isRat_of_adelic <;> assumption)
