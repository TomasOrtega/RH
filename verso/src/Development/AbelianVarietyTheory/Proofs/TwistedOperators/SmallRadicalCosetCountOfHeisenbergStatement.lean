import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.InertZeta.count_of_heis | exact GlobalTheory.InertZeta.count_of_heis | (intros; apply GlobalTheory.InertZeta.count_of_heis <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.smallRadicalCosetCount_of_heisenberg : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.InertZeta.count_of_heis | exact GlobalTheory.InertZeta.count_of_heis | (intros; apply GlobalTheory.InertZeta.count_of_heis <;> assumption)
