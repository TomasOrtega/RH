import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLevi
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviEmbeddingMemLevi.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | exact GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx | (intros; apply GlobalTheory.CompanionTheory.LeviBlockIdx.leviEmb_mem_levi_blockIdx <;> assumption)
