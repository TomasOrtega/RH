import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientLineDegreeLeOfTriangularFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.QuotLine.quot_line_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuotientLineDegreeLeOfTriangularFamily.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.quotient_line_degree_le_of_triangular_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → (∀ (v : Place k F) (i : Fin r), g v i.succ 0 = 0) → admitted (fun v => (g v).submatrix Fin.succ Fin.succ) → ∀ b : ℝ, LinesLE g b → LinesLE (fun v => (g v).submatrix Fin.succ Fin.succ) (2 * b - (∑ᶠ v, ord v (g v 0 0) : ℤ)) := by
  first | exact @GlobalTheory.Nef.QuotLine.quot_line_le | exact GlobalTheory.Nef.QuotLine.quot_line_le | (intros; apply GlobalTheory.Nef.QuotLine.quot_line_le <;> assumption)
