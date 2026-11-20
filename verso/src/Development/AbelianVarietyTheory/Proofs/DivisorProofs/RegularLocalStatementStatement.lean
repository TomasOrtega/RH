import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.DetHT.RegLoc.main | exact GlobalTheory.DetHT.RegLoc.main | (intros; apply GlobalTheory.DetHT.RegLoc.main <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.RegularLocalStatement : RegLocSt := by
  first | exact @GlobalTheory.DetHT.RegLoc.main | exact GlobalTheory.DetHT.RegLoc.main | (intros; apply GlobalTheory.DetHT.RegLoc.main <;> assumption)
