import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFive
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselConstantBoundsOfGeTwoNPowFive.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  first | exact @GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | exact GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five | (intros; apply GlobalTheory.SgInf.a_bounds_of_ge_two_n_pow_five <;> assumption)
