import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesOfFreePermute
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadCount.embReg_of_free_permuted_summands` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEmbedsInRegularRepresentationCopiesOfFreePermute.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∃ n : ℕ, EmbReg ρ H n ∧ n * Nat.card H = finrank K V := by
  first | exact @GlobalTheory.BadCount.embReg_of_free_permuted_summands | exact GlobalTheory.BadCount.embReg_of_free_permuted_summands | (intros; apply GlobalTheory.BadCount.embReg_of_free_permuted_summands <;> assumption)
