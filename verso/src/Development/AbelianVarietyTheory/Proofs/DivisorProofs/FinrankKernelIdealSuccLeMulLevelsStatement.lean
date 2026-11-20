import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealSuccLeMulLevels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankKernelIdealSuccLeMulLevels.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u : G ⟶ G) (n : ℕ), Module.finrank k (G.A (n + 1) ⧸ kerIdeal (u.app (n + 1))) ≤ Module.finrank k (G.A 1 ⧸ kerIdeal (u.app 1)) * Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le <;> assumption)
