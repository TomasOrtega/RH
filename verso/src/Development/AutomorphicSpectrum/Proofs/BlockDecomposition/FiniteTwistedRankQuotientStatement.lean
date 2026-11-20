import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteTwistedRankQuotient.lean&line=458#L458)
-/
theorem _root_.GlobalTheory.T.finite_twisted_rank_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (κ : ℕ), κ = Fintype.card c → ∀ θ : GL a k →* ℂˣ, Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | exact GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep <;> assumption)
