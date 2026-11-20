import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactor
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEmbeddedSmallNeighbourhoodFactor.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.embedded_small_neighbourhood_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
    ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
      ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | exact GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent <;> assumption)
