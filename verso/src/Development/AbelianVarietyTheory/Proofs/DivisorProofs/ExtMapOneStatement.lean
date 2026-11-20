import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExtOne.extMap_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExtMapOne.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.extMap_one' : ∀ {m : ℕ}, extMap (1 : Matrix (Fin m) (Fin m) ℂ) = ContinuousLinearMap.id ℂ (Ext m) := by
  first | exact @GlobalTheory.ExtOne.extMap_one | exact GlobalTheory.ExtOne.extMap_one | (intros; apply GlobalTheory.ExtOne.extMap_one <;> assumption)
