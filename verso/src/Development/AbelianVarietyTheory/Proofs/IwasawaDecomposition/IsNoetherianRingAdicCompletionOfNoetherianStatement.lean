import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsNoetherianRingAdicCompletionOfNoetherian.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by
  first | exact @GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | exact GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | (intros; apply GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion <;> assumption)
