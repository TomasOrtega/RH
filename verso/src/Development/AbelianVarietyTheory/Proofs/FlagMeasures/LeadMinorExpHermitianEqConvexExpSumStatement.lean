import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLeadMinorExpHermitianEqConvexExpSum.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n), ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧ ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl = ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | exact GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum | (intros; apply GlobalTheory.LeadMinorExp.leadMinor_exp_eq_sum <;> assumption)
