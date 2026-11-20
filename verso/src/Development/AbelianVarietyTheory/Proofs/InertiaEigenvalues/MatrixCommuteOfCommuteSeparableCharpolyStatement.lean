import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommuteOfCommuteSeparableCharpoly
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CommSep.commute_of_commute_separable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMatrixCommuteOfCommuteSeparableCharpoly.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.matrix_commute_of_commute_separable_charpoly : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  first | exact @GlobalTheory.CommSep.commute_of_commute_separable | exact GlobalTheory.CommSep.commute_of_commute_separable | (intros; apply GlobalTheory.CommSep.commute_of_commute_separable <;> assumption)
