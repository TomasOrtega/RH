import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqAevalOfCommute
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixEqAevalOfCommute.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.matrix_eq_aeval_of_commute_of_charpoly_separable : ∀ {k : Type} [Field k] (n : ℕ) (N X : Matrix (Fin n) (Fin n) k), N.charpoly.Separable → Commute X N → ∃ q : Polynomial k, X = Polynomial.aeval N q := by
  first | exact @GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute | exact GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute | (intros; apply GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute <;> assumption)
