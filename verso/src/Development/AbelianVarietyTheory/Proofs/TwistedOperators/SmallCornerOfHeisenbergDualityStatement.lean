import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDuality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSmallCornerOfHeisenbergDuality.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_duality : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.InertZeta.smallCorner_of_heis_dual | exact GlobalTheory.InertZeta.smallCorner_of_heis_dual | (intros; apply GlobalTheory.InertZeta.smallCorner_of_heis_dual <;> assumption)
