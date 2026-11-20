import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumRowsInvCubeDerivWeierstrassP
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasSumRowsInvCubeDerivWeierstrassP.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | exact GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP <;> assumption)
