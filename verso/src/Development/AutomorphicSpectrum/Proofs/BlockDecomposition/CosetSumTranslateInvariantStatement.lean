import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariant
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosetSumTranslateInvariant.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.coset_sum_translate_invariant : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | exact GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | (intros; apply GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal <;> assumption)
