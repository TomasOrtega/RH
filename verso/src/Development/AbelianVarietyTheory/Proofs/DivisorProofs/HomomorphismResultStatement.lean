import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismResult
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.WeilHomGen.homSt | exact GlobalTheory.WeilHomGen.homSt | (intros; apply GlobalTheory.WeilHomGen.homSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.homomorphism_result : HomSt := by
  first | exact @GlobalTheory.WeilHomGen.homSt | exact GlobalTheory.WeilHomGen.homSt | (intros; apply GlobalTheory.WeilHomGen.homSt <;> assumption)
