import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlRepresentativesRightMulPerm
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeUlRepresentativesRightMulPerm.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.heckeUlRepresentatives_right_mul_perm : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → ∀ γ : Lev N l, ∃ π : Equiv.Perm (Fin l), ∀ i, ∃ γ' : Lev N l, ulFam l i * mat γ = mat γ' * ulFam l (π i) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulFam_perm | exact GlobalTheory.HeckeFamilyMatrices.ulFam_perm | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulFam_perm <;> assumption)
