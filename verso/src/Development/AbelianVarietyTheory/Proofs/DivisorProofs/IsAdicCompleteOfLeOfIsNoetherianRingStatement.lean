import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAdicCompleteOfLeOfIsNoetherianRing.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I J : Ideal R), I ≤ J → IsAdicComplete J R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)
