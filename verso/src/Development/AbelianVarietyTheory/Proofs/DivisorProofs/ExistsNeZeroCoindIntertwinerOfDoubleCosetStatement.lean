import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCoset
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNeZeroCoindIntertwinerOfDoubleCoset.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_coindIntertwiner_of_doubleCoset : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  first | exact @GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | exact GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | (intros; apply GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset <;> assumption)
