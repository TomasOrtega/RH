import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfCompletionFlat
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompletionFlat.flat_of_finite_of_flat_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFlatOfCompletionFlat.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.flat_of_completion_flat : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] (ψ : AdicCompletion (maximalIdeal A) A →+* R), ψ.Finite → (ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A))).Flat → ψ.Flat := by
  first | exact @GlobalTheory.CompletionFlat.flat_of_finite_of_flat_comp | exact GlobalTheory.CompletionFlat.flat_of_finite_of_flat_comp | (intros; apply GlobalTheory.CompletionFlat.flat_of_finite_of_flat_comp <;> assumption)
