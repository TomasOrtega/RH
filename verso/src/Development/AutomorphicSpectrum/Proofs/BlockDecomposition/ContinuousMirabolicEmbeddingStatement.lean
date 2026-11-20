import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousMirabolicEmbedding.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.continuous_mirabolic_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM <;> assumption)
