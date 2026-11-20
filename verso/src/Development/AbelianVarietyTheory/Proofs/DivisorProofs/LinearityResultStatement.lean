import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearityResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.linSt | exact GlobalTheory.HalfGeo.linSt | (intros; apply GlobalTheory.HalfGeo.linSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.linearity_result : LinSt := by
  first | exact @GlobalTheory.HalfGeo.linSt | exact GlobalTheory.HalfGeo.linSt | (intros; apply GlobalTheory.HalfGeo.linSt <;> assumption)
