import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBijectiveIntertwinerSubrepEquiv.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.bijective_intertwiner_subrep_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (S : Subrepresentation ρ) (O : S.toSubmodule →ₗ[ℂ] W), Function.Bijective O → (∀ (g : G) (v : S.toSubmodule), O ⟨ρ g v, S.apply_mem_toSubmodule g v.2⟩ = τ g (O v)) → Nonempty ((subQuot S ⊥).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | exact GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | (intros; apply GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective <;> assumption)
