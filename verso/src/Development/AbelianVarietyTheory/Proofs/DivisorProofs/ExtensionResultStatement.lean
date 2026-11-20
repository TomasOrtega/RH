import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.extSt | exact GlobalTheory.HalfGeo.extSt | (intros; apply GlobalTheory.HalfGeo.extSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.extension_result : ExtSt := by
  first | exact @GlobalTheory.HalfGeo.extSt | exact GlobalTheory.HalfGeo.extSt | (intros; apply GlobalTheory.HalfGeo.extSt <;> assumption)
