import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HalfGeo.liftSt | exact GlobalTheory.HalfGeo.liftSt | (intros; apply GlobalTheory.HalfGeo.liftSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.lifting_result : LiftSt := by
  first | exact @GlobalTheory.HalfGeo.liftSt | exact GlobalTheory.HalfGeo.liftSt | (intros; apply GlobalTheory.HalfGeo.liftSt <;> assumption)
