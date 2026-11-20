import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | exact GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | (intros; apply GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  first | exact @GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | exact GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map | (intros; apply GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map <;> assumption)
