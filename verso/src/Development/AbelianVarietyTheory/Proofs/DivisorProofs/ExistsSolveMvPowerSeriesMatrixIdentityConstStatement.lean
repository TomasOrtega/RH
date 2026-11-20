import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConst
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSolveMvPowerSeriesMatrixIdentityConst.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_solve_mvPowerSeries_matrix_identity_const : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  first | exact @GlobalTheory.powerSeries_matrix_solve | exact GlobalTheory.powerSeries_matrix_solve | (intros; apply GlobalTheory.powerSeries_matrix_solve <;> assumption)
