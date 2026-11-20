import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterate
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DworkGhost.exists_witt_ghost_iterate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsWittVectorGhostEqFrobeniusIterate.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
