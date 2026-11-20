import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicPeriodMatrix
import Mathlib
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.holomorphic_coordinates_in_holomorphic_frame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsHolomorphicPeriodMatrix.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_holomorphic_period_matrix : ∀ (n g : ℕ) (U : Set (Fin n → ℂ)) (E F : (Fin n → ℂ) → Fin g → Fin g → ℂ), DifferentiableOn ℂ E U → DifferentiableOn ℂ F U → (∀ s ∈ U, (Matrix.of fun k i => E s i k).det ≠ 0) → ∃ τ : (Fin n → ℂ) → Fin g → Fin g → ℂ, DifferentiableOn ℂ τ U ∧ ∀ s ∈ U, ∀ j, F s j = ∑ i, τ s i j • E s i := by
  first | exact @GlobalTheory.holomorphic_coordinates_in_holomorphic_frame | exact GlobalTheory.holomorphic_coordinates_in_holomorphic_frame | (intros; apply GlobalTheory.holomorphic_coordinates_in_holomorphic_frame <;> assumption)
