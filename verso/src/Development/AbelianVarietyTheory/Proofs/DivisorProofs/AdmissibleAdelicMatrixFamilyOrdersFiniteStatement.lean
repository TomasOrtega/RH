import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.lineFin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdmissibleAdelicMatrixFamilyOrdersFinite.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  first | exact @GlobalTheory.Nef.lineFin | exact GlobalTheory.Nef.lineFin | (intros; apply GlobalTheory.Nef.lineFin <;> assumption)
