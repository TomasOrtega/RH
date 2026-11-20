import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMap
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoindKernel.exists_kernel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInjectiveKernelCoindIntertwiningMap.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  first | exact @GlobalTheory.CoindKernel.exists_kernel | exact GlobalTheory.CoindKernel.exists_kernel | (intros; apply GlobalTheory.CoindKernel.exists_kernel <;> assumption)
