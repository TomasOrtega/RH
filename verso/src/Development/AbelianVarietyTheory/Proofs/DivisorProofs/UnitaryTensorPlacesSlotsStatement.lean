import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTensorPlacesSlots
import Mathlib

open Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.unitary_tensor_places_positions` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryTensorPlacesSlots.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) → (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈ Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by
  first | exact @GlobalTheory.unitary_tensor_places_positions | exact GlobalTheory.unitary_tensor_places_positions | (intros; apply GlobalTheory.unitary_tensor_places_positions <;> assumption)
