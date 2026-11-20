import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsExact
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CoinvExact.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteLengthCoinvariantsExact.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.finite_length_coinvariants_exact : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.CoinvExact.main | exact GlobalTheory.CompanionTheory.CoinvExact.main | (intros; apply GlobalTheory.CompanionTheory.CoinvExact.main <;> assumption)
