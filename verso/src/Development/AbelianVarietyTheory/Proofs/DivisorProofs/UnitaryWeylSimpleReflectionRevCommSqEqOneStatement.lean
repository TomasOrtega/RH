import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.simpleU_rev_and_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryWeylSimpleReflectionRevCommSqEqOne.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  first | exact @GlobalTheory.simpleU_rev_and_sq | exact GlobalTheory.simpleU_rev_and_sq | (intros; apply GlobalTheory.simpleU_rev_and_sq <;> assumption)
