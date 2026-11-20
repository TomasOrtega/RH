import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ExtOne.extMap_one | exact GlobalTheory.ExtOne.extMap_one | (intros; apply GlobalTheory.ExtOne.extMap_one <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.extMap_one' : ∀ {m : ℕ}, extMap (1 : Matrix (Fin m) (Fin m) ℂ) = ContinuousLinearMap.id ℂ (Ext m) := by
  first | exact @GlobalTheory.ExtOne.extMap_one | exact GlobalTheory.ExtOne.extMap_one | (intros; apply GlobalTheory.ExtOne.extMap_one <;> assumption)
