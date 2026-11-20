import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBall
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformTwistedInvarianceOnBall.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.uniform_twisted_invariance_on_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (M : ℤ), (∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) → ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) → v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi <;> assumption)
