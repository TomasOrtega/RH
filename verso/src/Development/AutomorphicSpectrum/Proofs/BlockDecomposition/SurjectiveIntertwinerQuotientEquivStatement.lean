import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSurjectiveIntertwinerQuotientEquiv.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.surjective_intertwiner_quotient_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (R : ρ.IntertwiningMap τ), Function.Surjective R → ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧ Nonempty ((subQuot ⊤ S).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | exact GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | (intros; apply GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv <;> assumption)
