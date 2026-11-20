import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSquaresLeTwoMulUnitsSquares
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIndexSquaresLeTwoMulUnitsSquares.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.index_squares_le_two_mul_units_squares : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K), w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 → (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧ (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_le | exact GlobalTheory.QNorm.index_sqs_top_le | (intros; apply GlobalTheory.QNorm.index_sqs_top_le <;> assumption)
