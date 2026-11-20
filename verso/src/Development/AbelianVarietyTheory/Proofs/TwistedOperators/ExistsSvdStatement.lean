import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsSvd.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ, B = U * (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  first | exact @GlobalTheory.RectSVD.exists_svd | exact GlobalTheory.RectSVD.exists_svd | (intros; apply GlobalTheory.RectSVD.exists_svd <;> assumption)
