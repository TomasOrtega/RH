import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegerCoordinatesBound
import Mathlib
open NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegerCoordinatesBound.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.integer_coordinates_bound : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)), Function.Surjective (fun i => InfinitePlace.mk (τ i)) → ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) → ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by
  first | exact @GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | exact GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le | (intros; apply GlobalTheory.CompanionTheory.NumberFieldCoord.abs_repr_le_of_forall_norm_embedding_le <;> assumption)
