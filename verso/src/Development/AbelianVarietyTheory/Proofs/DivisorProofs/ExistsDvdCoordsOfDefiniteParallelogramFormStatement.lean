import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_dvd_coords_of_definite_form` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDvdCoordsOfDefiniteParallelogramForm.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form : ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  first | exact @GlobalTheory.exists_dvd_coords_of_definite_form | exact GlobalTheory.exists_dvd_coords_of_definite_form | (intros; apply GlobalTheory.exists_dvd_coords_of_definite_form <;> assumption)
