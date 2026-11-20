import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernel
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GxSplit.gx_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FParahoricUnipotentTimesKernel.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.parahoric_unipotent_times_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  first | exact @GlobalTheory.CompanionTheory.GxSplit.gx_split | exact GlobalTheory.CompanionTheory.GxSplit.gx_split | (intros; apply GlobalTheory.CompanionTheory.GxSplit.gx_split <;> assumption)
