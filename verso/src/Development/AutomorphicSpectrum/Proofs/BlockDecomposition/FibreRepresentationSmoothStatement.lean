import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFibreRepresentationSmooth.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.fibre_representation_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
