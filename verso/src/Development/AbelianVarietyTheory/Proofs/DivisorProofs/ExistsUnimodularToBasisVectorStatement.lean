import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularToBasisVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnimodularToBasisVector.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_unimodular_to_basis_vector : ∀ {R : Type} [CommRing R] {r : ℕ} (a : Fin (r+1) → R) (l0 : Fin (r+1)), IsUnit (a l0) → ∃ Q : GL (Fin (r+1)) R, (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).mulVec a = (Pi.single 0 1 : Fin (r+1) → R) := by
  first | exact @GlobalTheory.column_unit_entry_to_first_basis_vector | exact GlobalTheory.column_unit_entry_to_first_basis_vector | (intros; apply GlobalTheory.column_unit_entry_to_first_basis_vector <;> assumption)
