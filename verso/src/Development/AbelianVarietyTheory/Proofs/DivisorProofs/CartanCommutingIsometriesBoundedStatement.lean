import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanCommutingIsometriesBounded
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCartanCommutingIsometriesBounded.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.cartan_commuting_isometries_bounded : ∀ {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ → ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, A.transpose * M * A.map star = M → A * θ = θ * A → ∀ i j, ‖A i j‖ ≤ R := by
  first | exact @GlobalTheory.isCartan_entries_bounded | exact GlobalTheory.isCartan_entries_bounded | (intros; apply GlobalTheory.isCartan_entries_bounded <;> assumption)
