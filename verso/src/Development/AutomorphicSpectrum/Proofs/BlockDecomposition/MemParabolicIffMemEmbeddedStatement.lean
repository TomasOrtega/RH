import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbedded
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMemParabolicIffMemEmbedded.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.mem_parabolic_iff_mem_embedded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)), y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | exact GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem <;> assumption)
