import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.mulP_flat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMulPFlat.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.mulP_flat' : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  first | exact @GlobalTheory.PDivGroup.mulP_flat | exact GlobalTheory.PDivGroup.mulP_flat | (intros; apply GlobalTheory.PDivGroup.mulP_flat <;> assumption)
