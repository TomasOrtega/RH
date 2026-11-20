import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecomp
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMulVecMidBlockDecomp.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.mulVec_mid_block_decomp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k), ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) = topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | exact GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.qp_mulVec_midV_exists_top <;> assumption)
