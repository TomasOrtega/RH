import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSumman
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardMulFinrankCharacterSpaceOfFreePermutedSumman.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  first | exact @GlobalTheory.BadCount.card_mul_finrank_eig_of_free | exact GlobalTheory.BadCount.card_mul_finrank_eig_of_free | (intros; apply GlobalTheory.BadCount.card_mul_finrank_eig_of_free <;> assumption)
