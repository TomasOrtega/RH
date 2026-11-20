import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDim
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeightLeCotangentDimAddDualCotangentDim.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  first | exact @GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | exact GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | (intros; apply GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual <;> assumption)
