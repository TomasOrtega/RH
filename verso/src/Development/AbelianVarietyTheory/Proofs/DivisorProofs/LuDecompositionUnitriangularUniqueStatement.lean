import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LuDecompositionUnitriangularUnique
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLuDecompositionUnitriangularUnique.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.lu_decomposition_unitriangular_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (A₁ A₂ N₁ U N₀ : Matrix (Fin m) (Fin m) R), (∀ i j, i < j → A₁ i j = 0) → (∀ i j, i < j → A₂ i j = 0) → (∀ i j, j < i → N₁ i j = 0) → (∀ i, N₁ i i = 1) → (∀ i j, j < i → U i j = 0) → (∀ i, U i i = 1) → (∀ i j, j < i → N₀ i j = 0) → (∀ i, N₀ i i = 1) → A₁ * A₂ * N₁ = U * N₀ → N₁ = U * N₀ := by
  first | exact @GlobalTheory.lu_unique | exact GlobalTheory.lu_unique | (intros; apply GlobalTheory.lu_unique <;> assumption)
