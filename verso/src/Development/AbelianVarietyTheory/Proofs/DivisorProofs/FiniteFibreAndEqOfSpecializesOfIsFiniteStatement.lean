import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreAndEqOfSpecializesOfIsFinite
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteFibreAndEqOfSpecializesOfIsFinite.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finite_fibre_and_eq_of_specializes_of_isFinite' : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  first | exact @GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | exact GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | (intros; apply GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite <;> assumption)
