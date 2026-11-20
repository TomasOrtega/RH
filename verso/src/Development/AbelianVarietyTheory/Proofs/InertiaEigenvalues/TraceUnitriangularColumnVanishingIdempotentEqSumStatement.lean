import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSum
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTraceUnitriangularColumnVanishingIdempotentEqSum.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k : ℕ), 1 ≤ k → k < N → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ' g N k ψ) χ = (∑ i ∈ Finset.range k, wh ψ (der ψ i χ) * ((g : ℂ) ^ (k - i) - (g : ℂ) ^ (k - i - 1))) + wh ψ (der ψ k χ) := by
  first | exact @GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der | exact GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der | (intros; apply GlobalTheory.GLq.ExactMult.tr_eJ'_eq_sum_wh_der <;> assumption)
