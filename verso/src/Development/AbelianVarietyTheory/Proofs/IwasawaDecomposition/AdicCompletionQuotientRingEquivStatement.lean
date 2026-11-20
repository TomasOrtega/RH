import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionQuotientRingEquiv
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAdicCompletionQuotientRingEquiv.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J q : Ideal A), Nonempty ((AdicCompletion J A ⧸ q.map (algebraMap A (AdicCompletion J A))) ≃+* AdicCompletion (J.map (Ideal.Quotient.mk q)) (A ⧸ q)) := by
  first | exact @GlobalTheory.adicCompletion_quotient_ringEquiv | exact GlobalTheory.adicCompletion_quotient_ringEquiv | (intros; apply GlobalTheory.adicCompletion_quotient_ringEquiv <;> assumption)
