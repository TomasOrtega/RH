import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.trIdem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGroupAlgebraTraceIdempotentAndIrreducibleDegree.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ), (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧ (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  first | exact @GlobalTheory.GLq.trIdem | exact GlobalTheory.GLq.trIdem | (intros; apply GlobalTheory.GLq.trIdem <;> assumption)
