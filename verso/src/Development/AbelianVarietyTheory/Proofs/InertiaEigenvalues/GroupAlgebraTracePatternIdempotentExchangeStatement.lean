import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchange
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGroupAlgebraTracePatternIdempotentExchange.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
