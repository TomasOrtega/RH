import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparable
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalRingExistsAevalOfCommuteSeparable.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.localRing_exists_aeval_of_commute_separable : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R), Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := by
  first | exact @GlobalTheory.LocalCommutant.exists_aeval_of_comm | exact GlobalTheory.LocalCommutant.exists_aeval_of_comm | (intros; apply GlobalTheory.LocalCommutant.exists_aeval_of_comm <;> assumption)
