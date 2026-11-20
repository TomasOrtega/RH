import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegComplexBaseChangeEq
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.trdeg_complex_baseChange_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTrdegComplexBaseChangeEq.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.trdeg_tensor_complex_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' := by
  first | exact @GlobalTheory.trdeg_complex_baseChange_eq | exact GlobalTheory.trdeg_complex_baseChange_eq | (intros; apply GlobalTheory.trdeg_complex_baseChange_eq <;> assumption)
