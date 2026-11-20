import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I J : Ideal R), I ≤ J → IsAdicComplete J R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)
