import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSumEigenvaluesNoncompactPartLe
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAbsSumEigenvaluesNoncompactPartLe.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤ Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  first | exact @GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | exact GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | (intros; apply GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le <;> assumption)
