import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsRegularLocalRingAdicCompletion.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isRegularLocalRing_adicCompletion' : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | exact GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | (intros; apply GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion <;> assumption)
