import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantsFiniteOfSmoothLevi
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCoinvariantsFiniteOfSmoothLevi.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.coinvariants_finite_of_smooth_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | exact GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd <;> assumption)
