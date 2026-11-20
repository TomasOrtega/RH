import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaGLLen.fibStr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FOmegaEquivInducedFibre.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.omega_equiv_induced_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | exact GlobalTheory.CompanionTheory.ThetaGLLen.fibStr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.fibStr <;> assumption)
