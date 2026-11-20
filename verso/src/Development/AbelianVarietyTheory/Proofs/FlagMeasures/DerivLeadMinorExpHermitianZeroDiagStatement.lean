import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiag
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDerivLeadMinorExpHermitianZeroDiag.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.MinorJet.deriv_leadMinor_exp | exact GlobalTheory.MinorJet.deriv_leadMinor_exp | (intros; apply GlobalTheory.MinorJet.deriv_leadMinor_exp <;> assumption)
