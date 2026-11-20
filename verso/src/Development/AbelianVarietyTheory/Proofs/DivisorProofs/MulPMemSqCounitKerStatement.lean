import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.mulP_mem_sq_counit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMulPMemSqCounitKer.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.mulP_mem_sq_counit_ker : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  first | exact @GlobalTheory.PDivGroup.mulP_mem_sq_counit | exact GlobalTheory.PDivGroup.mulP_mem_sq_counit | (intros; apply GlobalTheory.PDivGroup.mulP_mem_sq_counit <;> assumption)
