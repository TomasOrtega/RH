import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxForm.DelForm.isForm_del` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolAtlasIsFormDel.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.holAtlas_isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → A.IsForm (A.del α) := by
  first | exact @GlobalTheory.CxForm.DelForm.isForm_del | exact GlobalTheory.CxForm.DelForm.isForm_del | (intros; apply GlobalTheory.CxForm.DelForm.isForm_del <;> assumption)
