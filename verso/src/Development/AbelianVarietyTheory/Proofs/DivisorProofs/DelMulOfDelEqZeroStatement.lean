import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelMulOfDelEqZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDelMulOfDelEqZero.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.del_mul_of_del_eq_zero' : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  first | exact @GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero | exact GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero | (intros; apply GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero <;> assumption)
