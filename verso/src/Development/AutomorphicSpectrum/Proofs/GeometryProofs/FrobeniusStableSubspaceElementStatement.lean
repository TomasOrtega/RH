import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElement
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFrobeniusStableSubspaceElement.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.frobenius_stable_subspace_element : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  first | exact @GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | exact GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | (intros; apply GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed <;> assumption)
