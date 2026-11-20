import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_perm_isUnit_leading_minors_localRing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPermutationLeadingMinors.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_permutation_leading_minors : ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R), IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m), IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  first | exact @GlobalTheory.exists_perm_isUnit_leading_minors_localRing | exact GlobalTheory.exists_perm_isUnit_leading_minors_localRing | (intros; apply GlobalTheory.exists_perm_isUnit_leading_minors_localRing <;> assumption)
