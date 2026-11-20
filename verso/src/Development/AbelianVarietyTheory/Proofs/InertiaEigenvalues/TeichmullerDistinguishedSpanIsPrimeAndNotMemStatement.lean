import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedSpanIsPrimeAndNotMem
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTeichmullerDistinguishedSpanIsPrimeAndNotMem.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.teichmullerDistinguished_span_isPrime_and_not_mem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → ¬ IsUnit x → IsAdicComplete (Ideal.span {x}) O → ∀ (e : ℕ) (w E' : WittVector l O), 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → (Ideal.span {E'}).IsPrime ∧ ((l : ℕ) : WittVector l O) ∉ Ideal.span {E'} := by
  first | exact @GlobalTheory.teichmuller_distinguished_span_isPrime | exact GlobalTheory.teichmuller_distinguished_span_isPrime | (intros; apply GlobalTheory.teichmuller_distinguished_span_isPrime <;> assumption)
