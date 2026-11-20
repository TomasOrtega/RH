import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHomogeneousDehomogenize
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsHomogeneousDehomogenize.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by
  first | exact @GlobalTheory.exists_isHomogeneous_dehomogenize | exact GlobalTheory.exists_isHomogeneous_dehomogenize | (intros; apply GlobalTheory.exists_isHomogeneous_dehomogenize <;> assumption)
